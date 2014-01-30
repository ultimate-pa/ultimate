package de.uni_freiburg.informatik.ultimate.access;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.walker.CFGWalker;
import de.uni_freiburg.informatik.ultimate.access.walker.DFSTreeWalker;
import de.uni_freiburg.informatik.ultimate.access.walker.IWalker;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore.Ultimate_Mode;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.model.GraphNotFoundException;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IModelManager;

//@formatter:off
/**
 * PluginConnector executes observers of a single ITool tool in a toolchain. It
 * uses the following live cycle: - Select all desired models according to
 * tool.getQueryKeyword() - foreach model - tool.setInputDefinition() -
 * tool.getObservers() - execute each observer on the current model with -
 * observer.getWalkerOptions() - observer.init() - observer.run(model.Root) -
 * observer.finish() - if tool instanceof IGenerator, store model in
 * ModelManager by calling - tool.getModel() - tool.getOutputDefinition()
 * 
 * @author dietsch
 */
// @formatter:on
public class PluginConnector {

	private static Logger sLogger = UltimateServices.getInstance().getLogger(
			Activator.s_PLUGIN_ID);

	private IModelManager mModelManager;

	private IController mController;

	private ITool mTool;

	private boolean mHasPerformedChanges;

	private int mCurrent;
	private int mMax;

	public PluginConnector(IModelManager modelmanager, ITool tool,
			IController control) {
		mModelManager = modelmanager;
		mController = control;
		mTool = tool;
		init();
	}

	private void init() {
		mHasPerformedChanges = false;
		mCurrent = mMax = 0;
	}

	public void run() throws Exception {
		init();
		List<GraphType> models = selectModels();
		if (models.isEmpty()) {
			IllegalArgumentException ex = new IllegalArgumentException();
			sLogger.error("Tool did not select a valid model", ex);
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
	}

	public boolean hasPerformedChanges() {
		return mHasPerformedChanges;
	}

	public String toString() {
		return mTool.getName();
	}

	private void runTool(List<IObserver> observers, GraphType currentModel) {
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

	private void runObserver(IObserver observer, GraphType currentModel,
			IElement entryNode) {
		logObserverRun(observer, currentModel);
		IWalker walker = selectWalker(currentModel, observer.getWalkerOptions());
		walker.addObserver(observer);
		observer.init();
		walker.run(entryNode);
		observer.finish();
		mHasPerformedChanges = mHasPerformedChanges
				|| observer.performedChanges();
	}

	private void logObserverRun(IObserver observer, GraphType model) {
		StringBuilder sb = new StringBuilder();
		sb.append("Executing the observer ");
		sb.append(observer.getClass().getSimpleName());
		sb.append(" from plugin ");
		sb.append(mTool.getName());
		sb.append(" for \"");
		sb.append(model);
		sb.append("\" (");
		sb.append(mCurrent);
		sb.append("/");
		sb.append(mMax);
		sb.append(") ...");
		sLogger.info(sb.toString());
	}

	private IElement getEntryPoint(GraphType definition) {
		IElement n = null;
		try {
			n = mModelManager.getRootNode(definition);
		} catch (GraphNotFoundException e) {
			sLogger.error("Graph not found!", e);
		}
		return n;
	}

	private void retrieveModel(IGenerator tool, String observer) {
		IElement element = tool.getModel();
		GraphType type = tool.getOutputDefinition();
		if (element != null && type != null) {
			mModelManager.addItem(element, type);
		} else {
			sLogger.error(tool.getName()
					+ " did return invalid model for observer " + observer
					+ ", skipping insertion in model container");
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
				// In fallback mode, USER == LAST!
				if (UltimateServices.getInstance().getUltimateMode() == Ultimate_Mode.FALLBACK_CMDLINE) {
					models.add(mModelManager.getLastAdded());
				} else {
					for (String s : mController.selectModel(mModelManager
							.getItemNames())) {
						GraphType t = mModelManager.getGraphTypeById(s);
						if (t != null) {
							models.add(t);
						}
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
			IllegalStateException ex = new IllegalStateException(
					"Unknown Query type");
			sLogger.fatal("Unknown Query type", ex);
			throw ex;
		}
		if (models.isEmpty()) {
			sLogger.warn("no suitable model selected, skipping...");
		}
		return models;
	}

	private IWalker selectWalker(GraphType currentModel, WalkerOptions options) {
		// TODO implement walker selection logics
		if (currentModel.getType().name().equals("CFG")) {
			return new CFGWalker();
		}
		return new DFSTreeWalker();
	}
}
