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
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CountDownLatch;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.GraphNotFoundException;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.StoreObjectException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainExceptionWrapper;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
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
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain.ReturnCode;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainProgressMonitor;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.results.ITimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainCancel;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
final class ToolchainWalker implements IToolchainCancel {

	private static final int INITIAL_COUNTDOWN = 2;

	private boolean mToolchainCancelRequest;
	private final ILogger mLogger;
	private final Map<String, PluginConnector> mOpenPlugins;
	private final Benchmark mBench;
	private final IModelManager mModelManager;
	private final PluginFactory mPluginFactory;
	private final CountDownLatch mCountDownLatch;

	ToolchainWalker(final Benchmark bench, final IModelManager mmanager, final PluginFactory factory,
			final ILogger logger) {
		assert logger != null;
		mBench = bench;
		mModelManager = mmanager;
		mLogger = logger;
		mPluginFactory = factory;
		mOpenPlugins = new HashMap<>();
		mCountDownLatch = new CountDownLatch(INITIAL_COUNTDOWN);
		mToolchainCancelRequest = false;
	}

	ReturnCode walk(final CompleteToolchainData data, final IProgressMonitorService service,
			final IToolchainProgressMonitor monitor) throws Throwable {
		if (mCountDownLatch.getCount() != INITIAL_COUNTDOWN) {
			throw new IllegalStateException("You cannot reuse the toolchain walker");
		}
		try {
			return walkUnprotected(data, service, monitor);
		} finally {
			mCountDownLatch.countDown();
			monitor.done();
		}
	}

	@Override
	public CountDownLatch cancelToolchain() {
		mToolchainCancelRequest = true;
		return mCountDownLatch;
	}

	/**
	 * The toolchain manager calls this method after he is finished processing this toolchain.
	 */
	void endToolchain() {
		mCountDownLatch.countDown();
	}

	private ReturnCode walkUnprotected(final CompleteToolchainData data, final IProgressMonitorService service,
			final IToolchainProgressMonitor monitor) throws Throwable {
		final IToolchainData<RunDefinition> chain = data.getToolchain();

		// convert monitor to submonitor
		int remainingWork = chain.getRootElement().getToolchain().getPluginOrSubchain().size();
		final SubMonitor progress = SubMonitor.convert(RcpProgressMonitorWrapper.create(monitor), remainingWork);
		mLogger.info("Walking toolchain with " + remainingWork + " elements.");

		// iterate over toolchain
		for (final Object toolchainElement : chain.getRootElement().getToolchain().getPluginOrSubchain()) {
			// Deal with the current toolchain element
			final ReturnCode returnCode;
			if (toolchainElement instanceof PluginType) {
				final PluginType plugin = (PluginType) toolchainElement;
				if (shouldCancel(data, service, monitor, plugin.getId())) {
					return ReturnCode.Cancel;
				}
				returnCode = processPlugin(data, plugin);
				// each successful plugin advances progress bar by 1
				progress.worked(1);
				remainingWork--;
				progress.setWorkRemaining(remainingWork);
			} else if (toolchainElement instanceof SubchainType) {
				final SubchainType subchain = (SubchainType) toolchainElement;
				if (shouldCancel(data, service, monitor, subchain.toString())) {
					return ReturnCode.Cancel;
				}
				// a subchain starts a subprocess that may consume 1 tick
				returnCode = processSubchain(data, subchain, progress.newChild(1));
				progress.worked(1);
				remainingWork--;
				progress.setWorkRemaining(remainingWork);
			} else {
				if (toolchainElement != null) {
					mLogger.warn("Unknown toolchain element " + toolchainElement.getClass().getSimpleName()
							+ ", skipping...");
				} else {
					mLogger.warn("Toolchain element is NULL, skipping...");
				}
				returnCode = ReturnCode.Ok;
			}

			switch (returnCode) {
			case Cancel:
			case Error:
				return returnCode;
			case Ok:
				break;
			default:
				throw new UnsupportedOperationException("Unknown return code");
			}
		}
		return ReturnCode.Ok;
	}

	private boolean shouldCancel(final CompleteToolchainData data, final IProgressMonitorService service,
			final IToolchainProgressMonitor monitor, final String pluginId) {
		// If a cancel-request occurred during the loop, honor it
		if (mToolchainCancelRequest || monitor.isCanceled()) {
			mLogger.info("Toolchain execution was canceled (user or tool) before executing " + pluginId);
			return true;
		}

		if (!service.continueProcessingRoot()) {
			final Collection<ITimeoutResult> toResults = ResultUtil.filterResults(
					data.getToolchain().getServices().getResultService().getResults(), ITimeoutResult.class);
			if (toResults.isEmpty()) {
				data.getToolchain().getServices().getResultService().reportResult(Activator.PLUGIN_ID,
						new TimeoutResult(Activator.PLUGIN_ID, "Timeout occured before executing " + pluginId));
			}
			mLogger.info("Toolchain execution was canceled (Timeout) before executing " + pluginId);
			return true;
		}
		return false;
	}

	/**
	 * Process the specified plug-in and handle all exceptions along the way.
	 */
	private ReturnCode processPlugin(final CompleteToolchainData data, final PluginType plugin) {

		// get tool belonging to id
		final ITool tool = mPluginFactory.createTool(plugin.getId());
		if (tool == null) {
			mLogger.error("Couldn't identify tool for plugin id " + plugin.getId() + "!");
			mToolchainCancelRequest = true;
			return ReturnCode.Cancel;
		}

		final PluginConnector pc;
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
		return executePluginConnector(data, plugin, pc);
	}

	private ReturnCode executePluginConnector(final CompleteToolchainData data, final PluginType plugin,
			final PluginConnector pc) {
		try {
			pc.run();
			return ReturnCode.Ok;
		} catch (final Throwable e) {
			return handleException(data, plugin, e);
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

	private ReturnCode handleException(final CompleteToolchainData data, final PluginType plugin,
			final ToolchainCanceledException e) {
		mLogger.info("Toolchain cancelled while executing plugin " + plugin.getId() + ". Reason: " + e.getMessage());
		final String longDescription = "Toolchain cancelled " + e.printRunningTaskMessage();
		final TimeoutResult timeoutResult = new TimeoutResult(plugin.getId(), longDescription);
		data.getToolchain().getServices().getResultService().reportResult(plugin.getId(), timeoutResult);
		return ReturnCode.Cancel;
	}

	private ReturnCode handleException(final CompleteToolchainData data, final PluginType plugin,
			final SMTLIBException e) {
		mLogger.fatal("An unrecoverable error occured during an interaction with an SMT solver:", e);
		reportExceptionOrError(data, plugin.getId(), e);
		return ReturnCode.Error;
	}

	private ReturnCode handleException(final CompleteToolchainData data, final PluginType plugin,
			final ToolchainExceptionWrapper e) {
		mLogger.fatal("A wrapped exception occured:", e);
		return handleException(data, plugin, e.getCause());
	}

	private ReturnCode handleException(final CompleteToolchainData data, final PluginType plugin,
			final Throwable cause) {
		if (cause instanceof ToolchainExceptionWrapper) {
			return handleException(data, plugin, (ToolchainExceptionWrapper) cause);
		} else if (cause instanceof SMTLIBException) {
			return handleException(data, plugin, (SMTLIBException) cause);
		} else if (cause instanceof ToolchainCanceledException) {
			return handleException(data, plugin, (ToolchainCanceledException) cause);
		} else {
			return handleExceptionFallback(data, plugin, cause);
		}
	}

	private ReturnCode handleExceptionFallback(final CompleteToolchainData data, final PluginType plugin,
			final Throwable e) {
		final String pluginId = plugin.getId();
		mLogger.fatal("The Plugin " + pluginId + " has thrown an exception:", e);
		reportExceptionOrError(data, pluginId, e);
		return ReturnCode.Error;
	}

	private static void reportExceptionOrError(final CompleteToolchainData data, final String pluginId,
			final Throwable e) {
		data.getToolchain().getServices().getResultService().reportResult(pluginId,
				new ExceptionOrErrorResult(pluginId, e));
	}

	/**
	 * Process a subchain statement in the toolchain
	 */
	private ReturnCode processSubchain(final CompleteToolchainData data, final SubchainType chain,
			final IProgressMonitor monitor) {
		mLogger.fatal("Subchain support is broken");
		return ReturnCode.Error;
	}

	/**
	 * process a serialize statement in toolchain
	 *
	 * @param serializeType
	 */
	private void processSerializeStmt(final CompleteToolchainData data, final SerializeType serializeType) {
		final List<ModelType> models = new ArrayList<>();
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
