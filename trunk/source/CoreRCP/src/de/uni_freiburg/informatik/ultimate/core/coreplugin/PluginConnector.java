package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.access.walker.CFGWalker;
import de.uni_freiburg.informatik.ultimate.access.walker.DFSTreeWalker;
import de.uni_freiburg.informatik.ultimate.access.walker.IWalker;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IToolchainPlugin;
import de.uni_freiburg.informatik.ultimate.model.GraphNotFoundException;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IModelManager;

//@formatter:off
/**
 * PluginConnector executes observers of a single {@link ITool} in a
 * {@link ToolchainData}. It uses the following live cycle:
 * <ul>
 * <li>Select all desired models according to {@link ITool#getQueryKeyword()}
 * <li>foreach model
 * <ul>
 * <li> {@link ITool#setInputDefinition(GraphType)}
 * <li> {@link ITool#getObservers()}
 * <li>execute each {@link IObserver} on the current model with
 * <ul>
 * <li> {@link IObserver#getWalkerOptions()}
 * <li> {@link IObserver#init()}
 * <li>use an {@link IWalker} to run {@link IObserver} on model
 * <li> {@link IObserver#finish()}
 * <li>if tool is an instance of {@link IGenerator}, store model in the
 * ModelManager by first calling {@link IGenerator#getModel()} and then calling
 * {@link IGenerator#getOutputDefinition()}
 * </ul>
 * </ul>
 * </ul>
 * 
 * @author dietsch
 */
// @formatter:on
public class PluginConnector {

	private Logger mLogger;

	private IModelManager mModelManager;
	private IController mController;
	private ITool mTool;

	private boolean mHasPerformedChanges;

	private int mCurrent;
	private int mMax;

	private IToolchainStorage mStorage;
	private IUltimateServiceProvider mServices;

	public PluginConnector(IModelManager modelmanager, ITool tool, IController control, IToolchainStorage storage,
			IUltimateServiceProvider services) {
		assert storage != null;
		assert control != null;
		assert modelmanager != null;
		assert tool != null;
		assert services != null;

		mModelManager = modelmanager;
		mController = control;
		mTool = tool;
		mStorage = storage;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		init();
	}

	private void init() {
		mHasPerformedChanges = false;
		mCurrent = mMax = 0;
	}

	public void run() throws Throwable {
		mLogger.info("------------------------" + mTool.getPluginName() + "----------------------------");
		init();
		initializePlugin(mLogger, mTool, mServices, mStorage);
		List<GraphType> models = selectModels();
		if (models.isEmpty()) {
			IllegalArgumentException ex = new IllegalArgumentException();
			mLogger.error("Tool did not select a valid model", ex);
			throw ex;
		}
		mMax = models.size();
		mCurrent = 1;

		for (int i = mMax - 1; i >= 0; --i) {
			GraphType currentModel = models.get(i);
			mTool.setInputDefinition(currentModel);
			List<IObserver> observers = mTool.getObservers();
			runTool(observers, currentModel);
			++mCurrent;
		}
		mTool.finish();
		mLogger.info("------------------------ END " + mTool.getPluginName() + "----------------------------");
	}

	public boolean hasPerformedChanges() {
		return mHasPerformedChanges;
	}

	public String toString() {
		return mTool.getPluginName();
	}

	private void runTool(List<IObserver> observers, GraphType currentModel) throws Throwable {
		IElement entryNode = getEntryPoint(currentModel);

		if (mTool instanceof IGenerator) {
			IGenerator tool = (IGenerator) mTool;
			for (IObserver observer : observers) {
				runObserver(observer, currentModel, entryNode);
				retrieveModel(tool, observer.toString());
			}
		} else {
			for (IObserver observer : observers) {
				runObserver(observer, currentModel, entryNode);
			}
		}
	}

	private void runObserver(IObserver observer, GraphType currentModel, IElement entryNode) throws Throwable {
		logObserverRun(observer, currentModel);
		IWalker walker = selectWalker(currentModel, observer.getWalkerOptions());
		walker.addObserver(observer);
		observer.init();
		walker.run(entryNode);
		observer.finish();
		mHasPerformedChanges = mHasPerformedChanges || observer.performedChanges();
	}

	private void logObserverRun(IObserver observer, GraphType model) {
		StringBuilder sb = new StringBuilder();
		sb.append("Executing the observer ");
		sb.append(observer.getClass().getSimpleName());
		sb.append(" from plugin ");
		sb.append(mTool.getPluginName());
		sb.append(" for \"");
		sb.append(model);
		sb.append("\" (");
		sb.append(mCurrent);
		sb.append("/");
		sb.append(mMax);
		sb.append(") ...");
		mLogger.info(sb.toString());
	}

	private IElement getEntryPoint(GraphType definition) {
		IElement n = null;
		try {
			n = mModelManager.getRootNode(definition);
		} catch (GraphNotFoundException e) {
			mLogger.error("Graph not found!", e);
		}
		return n;
	}

	private void retrieveModel(IGenerator tool, String observer) {
		IElement element = tool.getModel();
		GraphType type = tool.getOutputDefinition();
		if (element != null && type != null) {
			mModelManager.addItem(element, type);
		} else {
			mLogger.warn(String.format(
					"%s did return invalid model for observer %s, skipping insertion in model container",
					tool.getPluginName(), observer));
		}
	}

	private List<GraphType> selectModels() {
		List<GraphType> models = new ArrayList<GraphType>();

		switch (mTool.getQueryKeyword()) {
		case ALL:
			models.addAll(mModelManager.getItemKeys());
			break;
		case USER:
			if (mModelManager.size() > 1) {
				for (String s : mController.selectModel(mModelManager.getItemNames())) {
					GraphType t = mModelManager.getGraphTypeById(s);
					if (t != null) {
						models.add(t);
					}
				}
			} else {
				models.add(mModelManager.getItemKeys().get(0));
			}
			break;
		case LAST:
			models.add(mModelManager.getLastAdded());
			break;
		case SOURCE:
			models.addAll(mModelManager.getItemKeys());
			for (GraphType t : models) {
				if (!t.isFromSource()) {
					models.remove(t);
				}
			}
			break;
		case TOOL:
			List<String> desiredToolIDs = mTool.getDesiredToolID();
			if (desiredToolIDs == null || desiredToolIDs.size() == 0) {
				break;
			} else {
				models.addAll(mModelManager.getItemKeys());
				List<GraphType> removeModels = new ArrayList<GraphType>();
				for (GraphType t : models) {
					if (!desiredToolIDs.contains(t.getCreator()))
						removeModels.add(t);
				}
				models.removeAll(removeModels);
				break;
			}
		default:
			IllegalStateException ex = new IllegalStateException("Unknown Query type");
			mLogger.fatal("Unknown Query type", ex);
			throw ex;
		}
		if (models.isEmpty()) {
			mLogger.warn("no suitable model selected, skipping...");
		}
		return models;
	}

	private IWalker selectWalker(GraphType currentModel, WalkerOptions options) {
		// TODO implement walker selection logics
		if (currentModel.getType().name().equals("CFG")) {
			return new CFGWalker(mLogger);
		}
		return new DFSTreeWalker(mLogger);
	}

	static void initializePlugin(Logger logger, IToolchainPlugin plugin, IUltimateServiceProvider services,
			IToolchainStorage storage) {
		logger.info("Initializing " + plugin.getPluginName() + "...");
		try {
			plugin.setServices(services);
			plugin.setToolchainStorage(storage);
			plugin.init();
			logger.info(plugin.getPluginName() + " initialized");
		} catch (Exception ex) {
			logger.fatal("Exception during initialization of " + plugin.getPluginName());
			throw ex;
		}
	}
}
