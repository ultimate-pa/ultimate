/*
 * Copyright (C) 2010-2015 Christian Simon
 * Copyright (C) 2012-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.CountDownLatch;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.GraphNotFoundException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.StoreObjectException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainExceptionWrapper;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.DropmodelType;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ModelIdOnlyType;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.PluginType;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.SerializeType;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.SubchainType;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ToolchainModelType;
import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.ITool;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainProgressMonitor;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainCancel;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

final class ToolchainWalker implements IToolchainCancel {

	/**
	 * Is a running toolchain supposed to be canceled at the next possible moment?
	 */
	private boolean mToolchainCancelRequest;

	private final ILogger mLogger;
	private final Map<String, PluginConnector> mOpenPlugins;
	private final Benchmark mBench;
	private final IModelManager mModelManager;
	private final PluginFactory mPluginFactory;
	private final CountDownLatch mCountDownLatch;

	public ToolchainWalker(final Benchmark bench, final IModelManager mmanager, final PluginFactory factory,
			final ILogger logger) {
		assert logger != null;
		mBench = bench;
		mModelManager = mmanager;
		mLogger = logger;
		mPluginFactory = factory;
		mOpenPlugins = new HashMap<>();
		mCountDownLatch = new CountDownLatch(1);
		mToolchainCancelRequest = false;
	}

	public void walk(final CompleteToolchainData data, final IProgressMonitorService service,
			final IToolchainProgressMonitor monitor) throws Throwable {
		try {
			walkUnprotected(data, service, monitor);
		} finally {
			mCountDownLatch.countDown();
			monitor.done();
		}
	}

	private void walkUnprotected(final CompleteToolchainData data, final IProgressMonitorService service,
			final IToolchainProgressMonitor monitor) throws Throwable {
		final IToolchainData<RunDefinition> chain = data.getToolchain();

		// convert monitor to submonitor
		int remainingWork = chain.getRootElement().getToolchain().getPluginOrSubchain().size();
		final SubMonitor progress = SubMonitor.convert(RcpProgressMonitorWrapper.create(monitor), remainingWork);
		mLogger.info("Walking toolchain with " + remainingWork + " elements.");

		// iterate over toolchain
		for (final Object o : chain.getRootElement().getToolchain().getPluginOrSubchain()) {

			// Deal with the current toolchain element
			if (o instanceof PluginType) {
				final PluginType plugin = (PluginType) o;
				if (shouldCancel(data, service, monitor, plugin.getId())) {
					return;
				}
				processPlugin(data, plugin);
				// each successful plugin advances progress bar by 1
				progress.worked(1);
				remainingWork--;
				progress.setWorkRemaining(remainingWork);
			} else if (o instanceof SubchainType) {
				final SubchainType subchain = (SubchainType) o;
				if (shouldCancel(data, service, monitor, subchain.toString())) {
					return;
				}
				// a subchain starts a subprocess that may consume 1 tick
				processSubchain(data, subchain, progress.newChild(1));
				progress.worked(1);
				remainingWork--;
				progress.setWorkRemaining(remainingWork);
			} else {
				if (o != null) {
					mLogger.warn("Unknown toolchain element " + o.getClass().getSimpleName() + ", skipping...");
				} else {
					mLogger.warn("Toolchain element is NULL, skipping...");
				}
				continue;
			}
		}
	}

	private boolean shouldCancel(final CompleteToolchainData data, final IProgressMonitorService service,
			final IToolchainProgressMonitor monitor, final String pluginId) {
		// If a cancel-request occurred during the loop, honor it
		if (mToolchainCancelRequest || monitor.isCanceled()) {
			mLogger.info("Toolchain execution was canceled (user or tool) before executing " + pluginId);
			return true;

		}

		if (!service.continueProcessing()) {
			data.getToolchain().getServices().getResultService().reportResult(Activator.PLUGIN_ID,
					new TimeoutResult(Activator.PLUGIN_ID, "Timeout occured before executing " + pluginId));
			mLogger.info("Toolchain execution was canceled (Timeout) before executing " + pluginId);
			return true;
		}

		return false;
	}

	/**
	 * Process the specified plug-in.
	 *
	 * @param plugin
	 * @return true/false, depending on whether plugin could be successfully processed
	 * @throws Exception
	 */
	private void processPlugin(final CompleteToolchainData data, final PluginType plugin) throws Throwable {

		// get tool belonging to id
		final ITool tool = mPluginFactory.createTool(plugin.getId());
		if (tool == null) {
			mLogger.error("Couldn't identify tool for plugin id " + plugin.getId() + "!");
			mToolchainCancelRequest = true;
			return;
		}

		PluginConnector pc;
		if (!mOpenPlugins.containsKey(plugin.getId())) {
			pc = new PluginConnector(mModelManager, tool, data.getController(), data.getToolchain().getStorage(),
					data.getToolchain().getServices());
			mOpenPlugins.put(plugin.getId(), pc);
		} else {
			pc = mOpenPlugins.get(plugin.getId());
		}

		if (mBench != null) {
			mBench.start(pc.toString());
		}

		try {
			pc.run();
		} catch (final ToolchainCanceledException e) {
			String longDescription =
					ToolchainCanceledException.MESSAGE + " while executing " + e.getClassOfThrower().getSimpleName();
			if (e.getRunningTaskInfo() != null) {
				longDescription += " during the following task: " + e.getRunningTaskInfo();
			}
			final TimeoutResult timeoutResult = new TimeoutResult(plugin.getId(), longDescription);
			data.getToolchain().getServices().getResultService().reportResult(plugin.getId(), timeoutResult);
			mLogger.info(
					"Toolchain cancelled while executing plugin " + plugin.getId() + ". Reason: " + e.getMessage());
		} catch (final Throwable e) {
			mLogger.error("The Plugin " + plugin.getId() + " has thrown an Exception!", e);
			throw new ToolchainExceptionWrapper(plugin.getId(), e);
		} finally {
			if (mBench != null) {
				mBench.stop(pc.toString());
			}
			// did the plug-in have a serialization child element?
			final SerializeType st = plugin.getSerialize();
			if (st != null) {
				processSerializeStmt(data, st);
			}

			// did the plug-in have a dropmodels child element?
			final DropmodelType dt = plugin.getDropmodels();
			if (dt != null) {
				processDropmodelStmt(data, dt);
			}

		}
	}

	/**
	 * Process a subchain statement in the toolchain
	 *
	 * @param chain
	 * @param monitor
	 * @return true/false, depending on whether subchain could be successfully processed
	 * @throws Exception
	 */
	private boolean processSubchain(final CompleteToolchainData data, final SubchainType chain,
			final IProgressMonitor monitor) throws Throwable {
		// again, convert monitor into SubMonitor with certain number of ticks
		// depending of length of subchain
		int workRemaining = chain.getPluginOrSubchain().size();
		final SubMonitor progress = SubMonitor.convert(monitor, workRemaining);

		// get first plugin if present
		final Optional<PluginType> firstpluginOpt = chain.getPluginOrSubchain().stream()
				.filter(o -> o instanceof PluginType).map(a -> (PluginType) a).findFirst();

		// Subchain has at least one normal plugin
		if (firstpluginOpt.isPresent()) {
			final String firstplugin = firstpluginOpt.get().getId();
			// document, whether toolchain has changed anything
			// which depends on outcome of first plugin in chain
			boolean changes;
			PluginConnector foo = mOpenPlugins.get(firstplugin);
			if (foo != null) {
				changes = foo.hasPerformedChanges();
			} else {
				changes = false;
			}

			// iterate over subchain until break
			// caused by first plugin
			while (true) {
				for (final Object o : chain.getPluginOrSubchain()) {
					if (monitor.isCanceled() || mToolchainCancelRequest) {
						mToolchainCancelRequest = true;
						return false;
					}
					if (o instanceof PluginType) {
						final PluginType plugin = (PluginType) o;
						processPlugin(data, plugin);
						progress.worked(1);
						workRemaining--;
						progress.setWorkRemaining(workRemaining);
					} else if (o instanceof SubchainType) {
						final SubchainType subchain = (SubchainType) o;
						// if chain has at least one plugin
						// return type of other Subchains is irrelevant
						processSubchain(data, subchain, progress.newChild(1));
						progress.worked(1);
						workRemaining--;
						progress.setWorkRemaining(workRemaining);
					} else {
						continue;
					}
				}

				foo = mOpenPlugins.get(firstplugin);
				boolean bar;
				if (foo != null) {
					bar = foo.hasPerformedChanges();
				} else {
					bar = false;
				}

				changes = changes || bar;

				if (!bar) {
					break;
				}
			}
			return changes;
			// subchain consists only of other subchains and no plugin
		}
		boolean changes = false;
		while (true) {

			boolean localchanges = false;
			for (final Object o : chain.getPluginOrSubchain()) {
				if (monitor.isCanceled() || mToolchainCancelRequest) {
					mToolchainCancelRequest = true;
					return false;
				}
				if (o instanceof SubchainType) {
					final SubchainType subchain = (SubchainType) o;
					final boolean foo = processSubchain(data, subchain, progress.newChild(1));
					localchanges = localchanges || foo;
					progress.worked(1);
					workRemaining--;
					progress.setWorkRemaining(workRemaining);
				} else {
					continue;
				}
			}
			// quit toolchain if all subchains
			// have returned false
			changes = changes || localchanges;
			if (!localchanges) {
				break;
			}
		}
		return changes;

	}

	/**
	 * process a serialize statement in toolchain
	 *
	 * @param serializeType
	 */
	private void processSerializeStmt(final CompleteToolchainData data, final SerializeType serializeType) {
		final ArrayList<ModelType> models = new ArrayList<>();
		if (serializeType.getParser() != null) {
			for (final ISource parser : data.getParsers()) {
				final ModelType graphType = mModelManager.getGraphTypeByGeneratorPluginId(parser.getPluginID());
				if (graphType != null) {
					models.add(graphType);
				} else {
					mLogger.warn("Parser model could not be found!");
				}
			}
		}
		for (final ToolchainModelType modelType : serializeType.getModel()) {
			final ModelType graphType;
			if ("mostrecent".equals(modelType.getId())) {
				graphType = mModelManager.getLastAdded();
			} else {
				graphType = mModelManager.getGraphTypeByGeneratorPluginId(modelType.getId());
			}
			if (graphType != null) {
				models.add(graphType);
			} else {
				mLogger.warn("Model " + modelType.getId() + " could not be found!");
			}
		}

		for (final ModelType model : models) {
			try {
				mLogger.debug("Attempting to serialize model " + model.toString() + " ...");
				mModelManager.persistAndDropExistingGraph(model);
				mLogger.debug("Persisting model succeeded.");
			} catch (final StoreObjectException e) {
				mLogger.error("An error occurred while persisting selected model", e);
			} catch (final GraphNotFoundException e) {
				mLogger.error("Specified graph could not be found.", e);
			}

		}
	}

	/**
	 * process a serialize statement in toolchain
	 *
	 * @param dt
	 */
	private void processDropmodelStmt(final CompleteToolchainData data, final DropmodelType dt) {
		if (dt.getParser() != null) {
			for (final ISource parser : data.getParsers()) {
				final ModelType model = mModelManager.getGraphTypeByGeneratorPluginId(parser.getPluginID());
				dropModel(model, parser.getPluginID());
			}
		}

		for (final ModelIdOnlyType modelId : dt.getModel()) {
			final ModelType model = mModelManager.getGraphTypeByGeneratorPluginId(modelId.getId());
			dropModel(model, modelId.getId());
		}
	}

	private void dropModel(final ModelType modelType, final String id) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Attempting to drop model " + id + " ...");
		}

		if (modelType == null || !mModelManager.removeItem(modelType)) {
			mLogger.warn("Failed to remove model " + id);
		} else if (mLogger.isDebugEnabled()) {
			mLogger.debug("Dropping model succeeded.");
		}
	}

	@Override
	public CountDownLatch cancelToolchain() {
		mToolchainCancelRequest = true;
		return mCountDownLatch;
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	static final class CompleteToolchainData {

		private final IToolchainData<RunDefinition> mToolchain;
		private final ISource[] mParsers;
		private final IController<RunDefinition> mController;

		CompleteToolchainData(final IToolchainData<RunDefinition> toolchain, final ISource[] parsers,
				final IController<RunDefinition> controller) {
			mToolchain = toolchain;
			mParsers = parsers;
			mController = controller;
		}

		IToolchainData<RunDefinition> getToolchain() {
			return mToolchain;
		}

		ISource[] getParsers() {
			return mParsers;
		}

		IController<RunDefinition> getController() {
			return mController;
		}
	}
}
