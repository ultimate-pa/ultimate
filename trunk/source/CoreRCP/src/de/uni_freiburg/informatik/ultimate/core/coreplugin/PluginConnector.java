/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.GraphNotFoundException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.modelwalker.CFGWalker;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.modelwalker.DFSTreeWalker;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.modelwalker.IWalker;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainPlugin;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

//@formatter:off
/**
 * PluginConnector executes observers of a single {@link ITool} in a
 * {@link ToolchainData}. It uses the following live cycle:
 * <ul>
 * <li>Select all desired models according to {@link ITool#getModelQuery()}
 * <li>foreach model
 * <ul>
 * <li> {@link ITool#setInputDefinition(ModelType)}
 * <li> {@link ITool#getObservers()}
 * <li>execute each {@link IObserver} on the current model with
 * <ul>
 * <li> {@link IObserver#getWalkerOptions()}
 * <li> {@link IObserver#init(ModelType, int, int)}
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

	private final ILogger mLogger;

	private final IModelManager mModelManager;
	private final IController<RunDefinition> mController;
	private final ITool mTool;

	private boolean mHasPerformedChanges;
	private final IToolchainStorage mStorage;
	private final IUltimateServiceProvider mServices;

	public PluginConnector(final IModelManager modelmanager, final ITool tool, final IController<RunDefinition> control,
			final IToolchainStorage storage, final IUltimateServiceProvider services) {
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
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		init();
	}

	private void init() {
		mHasPerformedChanges = false;
	}

	public void run() throws Throwable {
		mLogger.info("------------------------" + mTool.getPluginName() + "----------------------------");
		init();
		initializePlugin(mLogger, mTool, mServices, mStorage);
		final List<ModelType> models = selectModels();
		if (models.isEmpty()) {
			final IllegalArgumentException ex = new IllegalArgumentException();
			mLogger.error("Tool did not select a valid model", ex);
			throw ex;
		}
		final int max = models.size();
		int idx = 0;

		for (final ModelType currentModel : models) {
			mTool.setInputDefinition(currentModel);
			final List<IObserver> observers = mTool.getObservers();
			runTool(observers, currentModel, idx, max);
			++idx;
		}
		mTool.finish();
		mLogger.info("------------------------ END " + mTool.getPluginName() + "----------------------------");
	}

	public boolean hasPerformedChanges() {
		return mHasPerformedChanges;
	}

	@Override
	public String toString() {
		return mTool.getPluginName();
	}

	private void runTool(final List<IObserver> observers, final ModelType currentModel, final int currentModelIndex,
			final int numberOfModels) throws Throwable {
		final IElement entryNode = getEntryPoint(currentModel);

		if (mTool instanceof IGenerator) {
			final IGenerator tool = (IGenerator) mTool;
			for (final IObserver observer : observers) {
				runObserver(observer, currentModel, entryNode, currentModelIndex, numberOfModels);
				retrieveModel(tool, observer.toString());
			}
		} else {
			for (final IObserver observer : observers) {
				runObserver(observer, currentModel, entryNode, currentModelIndex, numberOfModels);
			}
		}
	}

	private void runObserver(final IObserver observer, final ModelType currentModel, final IElement entryNode,
			final int currentModelIndex, final int numberOfModels) throws Throwable {
		logObserverRun(observer, currentModel, currentModelIndex, numberOfModels);
		final IWalker walker = selectWalker(currentModel);
		walker.addObserver(observer);
		observer.init(currentModel, currentModelIndex, numberOfModels);
		walker.run(entryNode);
		observer.finish();
		mHasPerformedChanges = mHasPerformedChanges || observer.performedChanges();
	}

	private void logObserverRun(final IObserver observer, final ModelType model, final int idx, final int max) {
		final StringBuilder sb = new StringBuilder();
		sb.append("Executing the observer ");
		sb.append(observer.getClass().getSimpleName());
		sb.append(" from plugin ");
		sb.append(mTool.getPluginName());
		sb.append(" for \"");
		sb.append(model);
		sb.append("\" (");
		sb.append(idx + 1);
		sb.append("/");
		sb.append(max);
		sb.append(") ...");
		mLogger.info(sb.toString());
	}

	private IElement getEntryPoint(final ModelType definition) {
		IElement n = null;
		try {
			n = mModelManager.getRootNode(definition);
		} catch (final GraphNotFoundException e) {
			mLogger.error("Graph not found!", e);
		}
		return n;
	}

	private void retrieveModel(final IGenerator tool, final String observer) {
		final IElement element = tool.getModel();
		final ModelType type = tool.getOutputDefinition();
		if (element != null && type != null) {
			mLogger.info("Adding new model " + type + " " + element.getClass().getSimpleName());
			mModelManager.addItem(element, type);
		} else {
			mLogger.info(String.format(
					"Invalid model from %s for observer %s and model type %s, skipping insertion in model container",
					tool.getPluginName(), observer, type));
		}
	}

	private List<ModelType> selectModels() {
		final List<ModelType> models = new ArrayList<>();

		switch (mTool.getModelQuery()) {
		case ALL:
			models.addAll(mModelManager.getItemKeys());
			break;
		case USER:
			if (mModelManager.size() > 1) {
				for (final String s : mController.selectModel(mModelManager.getItemNames())) {
					final ModelType t = mModelManager.getGraphTypeById(s);
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
			for (final ModelType t : models) {
				if (!t.isFromSource()) {
					models.remove(t);
				}
			}
			break;
		case TOOL:
			final List<String> desiredToolIDs = mTool.getDesiredToolIds();
			if (desiredToolIDs == null || desiredToolIDs.isEmpty()) {
				break;
			}
			final Set<String> idSet = new HashSet<>(desiredToolIDs);
			mModelManager.getItemKeys().stream().filter(a -> idSet.contains(a.getCreator())).forEach(models::add);
			break;
		default:
			final IllegalStateException ex = new IllegalStateException("Unknown query type");
			mLogger.fatal("Unknown query type", ex);
			throw ex;
		}
		if (models.isEmpty()) {
			mLogger.warn("no suitable model selected, skipping...");
		}
		assert CoreUtil.isSorted(models.stream().map(ModelType::getCreated)
				.collect(Collectors.toList())) : "Available models are not sorted according to creation time";
		return models;
	}

	private IWalker selectWalker(final ModelType currentModel) {
		if ("CFG".equals(currentModel.getType().name())) {
			return new CFGWalker(mLogger);
		}
		return new DFSTreeWalker(mLogger);
	}

	static void initializePlugin(final ILogger logger, final IToolchainPlugin plugin,
			final IUltimateServiceProvider services, final IToolchainStorage storage) {
		logger.info("Initializing " + plugin.getPluginName() + "...");
		try {
			plugin.setServices(services);
			plugin.init();
			logger.info(plugin.getPluginName() + " initialized");
		} catch (final Exception ex) {
			logger.fatal("Exception during initialization of " + plugin.getPluginName());
			throw ex;
		}
	}

}
