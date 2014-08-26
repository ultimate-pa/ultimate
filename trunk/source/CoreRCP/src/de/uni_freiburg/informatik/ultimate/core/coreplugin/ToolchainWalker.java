package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.util.ArrayList;
import java.util.HashMap;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DropmodelType;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ModelIdOnlyType;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ModelType;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.PluginType;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.SerializeType;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.SubchainType;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainCancel;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;
import de.uni_freiburg.informatik.ultimate.model.GraphNotFoundException;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IModelManager;
import de.uni_freiburg.informatik.ultimate.model.repository.StoreObjectException;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

final class ToolchainWalker implements IToolchainCancel {

	/**
	 * Is a running toolchain supposed to be canceled at the next possible
	 * moment?
	 */
	private boolean mToolchainCancelRequest = false;

	private final Logger mLogger;
	private final HashMap<String, PluginConnector> mOpenPlugins;
	private final Benchmark mBench;
	private final IModelManager mModelManager;
	private final PluginFactory mPluginFactory;

	public ToolchainWalker(Benchmark bench, IModelManager mmanager, PluginFactory factory, Logger logger) {
		assert logger != null;
		mBench = bench;
		mModelManager = mmanager;
		mLogger = logger;
		mPluginFactory = factory;
		mOpenPlugins = new HashMap<String, PluginConnector>();
	}

	public void walk(CompleteToolchainData data, IProgressMonitorService service, IProgressMonitor monitor)
			throws Throwable {
		ToolchainData chain = data.getToolchain();

		// convert monitor to submonitor
		int work_remain = chain.getToolchain().getPluginOrSubchain().size();
		SubMonitor progress = SubMonitor.convert(monitor, work_remain);

		mLogger.info("Walking toolchain with " + String.valueOf(work_remain) + " elements.");

		// iterate over toolchain
		for (Object o : chain.getToolchain().getPluginOrSubchain()) {
			// If a cancel-request was initiated during the loop,
			// obey it!
			if (!service.continueProcessing() || monitor.isCanceled() || this.mToolchainCancelRequest) {
				mLogger.info("Toolchain execution was canceled (Timeout or user)");
				return;
			}
			// Otherwise deal with the current toolchain element
			if (o instanceof PluginType) {
				PluginType plugin = (PluginType) o;
				processPlugin(data, plugin);
				// each successful plugin advances progress bar by 1
				progress.worked(1);
				work_remain--;
				progress.setWorkRemaining(work_remain);
			} else if (o instanceof SubchainType) {
				SubchainType subchain = (SubchainType) o;
				// a subchain starts a subprocess that may consume 1 tick
				processSubchain(data, subchain, progress.newChild(1));
				progress.worked(1);
				work_remain--;
				progress.setWorkRemaining(work_remain);
			} else {
				continue;
			}
		}
		// TODO: DD: check if this is needed / correct.
		monitor.done();

	}

	/**
	 * Process the specified plug-in.
	 * 
	 * @param plugin
	 * @return true/false, depending on whether plugin could be successfully
	 *         processed
	 * @throws Exception
	 */
	private final void processPlugin(CompleteToolchainData data, PluginType plugin) throws Throwable {

		// get tool belonging to id
		ITool tool = mPluginFactory.createTool(plugin.getId());
		if (tool == null) {
			mLogger.error("Couldn't identify tool for plugin id " + plugin.getId() + "!");
			mToolchainCancelRequest = true;
			return;
		}

		PluginConnector pc;
		if (!mOpenPlugins.containsKey(plugin.getId())) {
			pc = new PluginConnector(mModelManager, tool, data.getController(), data.getToolchain().getStorage(), data
					.getToolchain().getServices());
			mOpenPlugins.put(plugin.getId(), pc);
		} else {
			pc = mOpenPlugins.get(plugin.getId());
		}

		if (mBench != null) {
			mBench.start(pc.toString());
		}

		try {
			pc.run();
		} catch (Throwable e) {
			if (e instanceof ToolchainCanceledException) {
				TimeoutResult timeoutResult = new TimeoutResult(plugin.getId(), e.getMessage());
				data.getToolchain().getServices().getResultService().reportResult(plugin.getId(), timeoutResult);
				mLogger.info("Toolchain cancelled while executing plugin" + plugin.getId() + ". Reason: "
						+ e.getMessage());
			} else {
				mLogger.error("The Plugin " + plugin.getId() + " has thrown an Exception!", e);
				throw e;
			}
		} finally {
			if (mBench != null) {
				mBench.stop(pc.toString());
			}
			// did the plug-in have a serialization child element?
			SerializeType st = plugin.getSerialize();
			if (st != null)
				processSerializeStmt(data, st);

			// did the plug-in have a dropmodels child element?
			DropmodelType dt = plugin.getDropmodels();
			if (dt != null)
				processDropmodelStmt(data, dt);

		}
	}

	/**
	 * process a Subchain statement in the toolchain
	 * 
	 * @param chain
	 * @param monitor
	 * @return true/false, depending on whether subchain could be successfully
	 *         processed
	 * @throws Exception
	 */
	private final boolean processSubchain(CompleteToolchainData data, SubchainType chain, IProgressMonitor monitor)
			throws Throwable {
		// again, convert monitor into SubMonitor with certain number of ticks
		// depending of length of subchain
		int work_remain = chain.getPluginOrSubchain().size();
		SubMonitor progress = SubMonitor.convert(monitor, work_remain);

		String firstplugin = null;

		// get first plugin if present
		for (Object o : chain.getPluginOrSubchain()) {
			if (o instanceof PluginType) {
				// we want to know the first plugin in the subchain!
				if (firstplugin == null) {
					PluginType foo = (PluginType) o;
					firstplugin = foo.getId();
					break;
				}
			}
		}

		// Subchain has at least one plugin
		if (firstplugin != null) {
			// document, whether toolchain has changed anything
			// which depends on outcome of first plugin in chain
			boolean changes;
			PluginConnector foo = mOpenPlugins.get(firstplugin);
			if (foo != null) {
				changes = foo.hasPerformedChanges();
			} else
				changes = false;

			// iterate over subchain until break
			// caused by first plugin
			while (true) {

				for (Object o : chain.getPluginOrSubchain()) {
					if (monitor.isCanceled() || this.mToolchainCancelRequest) {
						this.mToolchainCancelRequest = true;
						return false;
					}
					if (o instanceof PluginType) {
						PluginType plugin = (PluginType) o;
						processPlugin(data, plugin);
						progress.worked(1);
						work_remain--;
						progress.setWorkRemaining(work_remain);
					} else if (o instanceof SubchainType) {
						SubchainType subchain = (SubchainType) o;
						// if chain has at least one plugin
						// return type of other Subchains is irrelevant
						processSubchain(data, subchain, progress.newChild(1));
						progress.worked(1);
						work_remain--;
						progress.setWorkRemaining(work_remain);
					} else {
						continue;
					}
				}

				foo = mOpenPlugins.get(firstplugin);
				boolean bar;
				if (foo != null)
					bar = foo.hasPerformedChanges();
				else
					bar = false;

				changes = changes || bar;

				if (!bar) {
					break;
				}
			}
			return changes;

			// subchain consists only of other subchains and no plugin
		} else {
			boolean changes = false;
			while (true) {

				boolean localchanges = false;
				for (Object o : chain.getPluginOrSubchain()) {
					if (monitor.isCanceled() || this.mToolchainCancelRequest) {
						this.mToolchainCancelRequest = true;
						return false;
					}
					if (o instanceof SubchainType) {
						SubchainType subchain = (SubchainType) o;
						boolean foo = processSubchain(data, subchain, progress.newChild(1));
						localchanges = localchanges || foo;
						progress.worked(1);
						work_remain--;
						progress.setWorkRemaining(work_remain);
					} else {
						continue;
					}
				}
				// quit toolchain if all subchains
				// have returned false
				changes = changes || localchanges;
				if (localchanges == false)
					break;
			}
			return changes;
		}

	}

	/**
	 * process a serialize statement in toolchain
	 * 
	 * @param serializeType
	 */
	private final void processSerializeStmt(CompleteToolchainData data, SerializeType serializeType) {
		ArrayList<GraphType> models = new ArrayList<GraphType>();
		GraphType graphType = null;
		if (serializeType.getParser() != null) {
			graphType = mModelManager.getGraphTypeByGeneratorPluginId(data.getParser().getPluginID());
			if (graphType != null)
				models.add(graphType);
			else {
				mLogger.warn("Parser model could not be found!");
			}
		}
		for (ModelType modelType : serializeType.getModel()) {
			if (modelType.getId().equals("mostrecent")) {
				graphType = this.mModelManager.getLastAdded();
			} else {
				graphType = this.mModelManager.getGraphTypeByGeneratorPluginId(modelType.getId());
			}
			if (graphType != null)
				models.add(graphType);
			else
				mLogger.warn("Model " + modelType.getId() + " could not be found!");
		}
		for (GraphType model : models) {
			try {
				mLogger.debug("Attempting to serialize model " + model.toString() + " ...");
				this.mModelManager.persistAndDropExistingGraph(model);
				mLogger.debug("Persisting model succeeded.");
			} catch (StoreObjectException e) {
				mLogger.error("An error occurred while persisting selected model", e);
			} catch (GraphNotFoundException e) {
				mLogger.error("Specified graph could not be found.", e);
			}

		}
	}

	/**
	 * process a serialize statement in toolchain
	 * 
	 * @param dt
	 */
	private final void processDropmodelStmt(CompleteToolchainData data, DropmodelType dt) {
		if (dt.getParser() != null) {
			GraphType g = null;
			g = this.mModelManager.getGraphTypeByGeneratorPluginId(data.getParser().getPluginID());
			mLogger.debug("Attempting to drop parser model...");
			if (g != null) {
				boolean success = this.mModelManager.removeItem(g);

				if (success)
					mLogger.info("Dropping  model succeeded.");
				else
					mLogger.warn("Failed to remove parser model.");
			}
		}

		for (ModelIdOnlyType m : dt.getModel()) {
			GraphType g = null;
			g = this.mModelManager.getGraphTypeByGeneratorPluginId(m.getId());
			mLogger.debug("Attempting to drop model " + m.getId() + " ...");
			if (g == null) {
				mLogger.warn("Tried to remove a model that did not exist: " + m.getId() + ".");
				continue;
			}

			boolean success = this.mModelManager.removeItem(g);

			if (success)

				mLogger.info("Dropping  model succeeded.");
			else
				mLogger.warn("Failed to remove model " + m.getId() + ".");

		}
	}

	public void cancelToolchain() {
		mToolchainCancelRequest = true;
	}

	public HashMap<String, PluginConnector> getOpenPlugins() {
		return this.mOpenPlugins;
	}

	final class CompleteToolchainData {

		private ToolchainData mToolchain;
		private ISource mParser;
		private IController mController;

		CompleteToolchainData(ToolchainData toolchain, ISource parser, IController controller) {
			mToolchain = toolchain;
			mParser = parser;
			mController = controller;
		}

		final ToolchainData getToolchain() {
			return mToolchain;
		}

		final ISource getParser() {
			return mParser;
		}

		final IController getController() {
			return mController;
		}

	}

}
