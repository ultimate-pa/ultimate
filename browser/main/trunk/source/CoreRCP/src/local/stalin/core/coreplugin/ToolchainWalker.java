package local.stalin.core.coreplugin;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import local.stalin.access.PluginConnector;
import local.stalin.core.api.StalinServices;
import local.stalin.core.coreplugin.toolchain.DropmodelType;
import local.stalin.core.coreplugin.toolchain.ModelIdOnlyType;
import local.stalin.core.coreplugin.toolchain.ModelType;
import local.stalin.core.coreplugin.toolchain.PluginType;
import local.stalin.core.coreplugin.toolchain.SerializeType;
import local.stalin.core.coreplugin.toolchain.SubchainType;
import local.stalin.core.coreplugin.toolchain.Toolchain;
import local.stalin.ep.interfaces.IModifyingTool;
import local.stalin.ep.interfaces.IOutput;
import local.stalin.ep.interfaces.ITool;
import local.stalin.model.GraphNotFoundException;
import local.stalin.model.GraphType;
import local.stalin.model.IModelManager;
import local.stalin.model.MarkedTrace;
import local.stalin.model.repository.StoreObjectException;
import org.apache.log4j.Logger;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;

public class ToolchainWalker {
	
	/**
	 * Is a running toolchain supposed to be canceled at the next possible moment?
	 */
	private boolean m_ToolchainCancelRequest = false;
	
	private Logger s_Logger;
	
	/**
	 * Map of Tool ID to PluginConnector for plugins
	 * used by current toolchain.
	 */
	private HashMap<String, PluginConnector> m_OpenPlugins;
	
	
	/**
	 * Toolchain's internal variable that stores the traces
	 * returned by plugins implementing IModifyingTool.
	 */
	private List<MarkedTrace> m_MarkedTraces;
	
	// references to same-named objects in the Core
	// when they change in the core, they will also be 
	// changed here
	private Application m_Core;
	private Benchmark m_Bench;
	private IModelManager m_ModelManager;
	private HashMap<String, ITool> m_Id2Plugin;

	
	public ToolchainWalker(Application caller, Benchmark bench, IModelManager mmanager, HashMap<String, ITool> id2plugin) {
		m_Core = caller;
		m_Bench = bench;
		m_ModelManager = mmanager;
		m_Id2Plugin = id2plugin;
		s_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
		m_OpenPlugins = new HashMap<String, PluginConnector>();
		m_MarkedTraces = new LinkedList<MarkedTrace>();
	}
	
	public void walk(IProgressMonitor monitor) throws Exception {
		Toolchain chain = m_Core.getStoredToolchainUse();
		
		// convert monitor to submonitor
		int work_remain = chain.getToolchain().getPluginOrSubchain().size();
		SubMonitor progress = SubMonitor.convert(monitor, work_remain);
		
		s_Logger.info("Walking toolchain... with "+String.valueOf(work_remain)+" elements.");

		// iterate over toolchain
		for (Object o : chain.getToolchain().getPluginOrSubchain()) {
			// If a cancel-request was initiated during the loop,
			// obey it!
			if (monitor.isCanceled() || this.m_ToolchainCancelRequest) {
				return;
			}
			// Otherwise deal with the current toolchain element
			if (o instanceof PluginType) {
				PluginType plugin = (PluginType) o;
				processPlugin(plugin);
				// each successful plugin advances progress bar by 1
				progress.worked(1);
				work_remain--;
				progress.setWorkRemaining(work_remain);
			} else if (o instanceof SubchainType) {
				SubchainType subchain = (SubchainType) o;
				// a subchain starts a subprocess that may consume 1 tick
				processSubchain(subchain, progress.newChild(1));
				progress.worked(1);
				work_remain--;
				progress.setWorkRemaining(work_remain);
			} else {
				continue;
			}
		}
	}
	
	/**
	 * Process the specified plug-in.
	 * 
	 * @param plugin
	 */
	private final void processPlugin(PluginType plugin) {
		
		// get tool belonging to id
		ITool tool = this.m_Id2Plugin.get(plugin.getId());
		if (tool == null) {
			s_Logger.error("Couldn't identify tool for plugin id "
					+ plugin.getId() + "!");
			this.m_ToolchainCancelRequest = true;
			return;
		}
		tool.setTokenMap(m_Core.getParser().getTokenMap());
		
		// are we dealing with an Output Plugin?
		// if so, set the traces
		if (tool instanceof IOutput) {
			((IOutput) tool).setMarkedTraces(this.m_MarkedTraces);
		}
		
		
		PluginConnector pc;
		if (!m_OpenPlugins.containsKey(plugin.getId())) {
			pc = new PluginConnector(m_ModelManager, tool, m_Core.getController());
			m_OpenPlugins.put(plugin.getId(), pc);
		} else {
			pc = m_OpenPlugins.get(plugin.getId());
		}
		

		m_Bench.start(pc.toString());
		try {
			pc.run();
		} catch (Exception e) {
			s_Logger.error("The Plugin "+plugin.getId()+" has thrown an Exception!", e);
		}
		m_Bench.stop();
		// did the plug-in have a serialization child element?
		SerializeType st = plugin.getSerialize();
		if (st != null)
			processSerializeStmt(st);
		
		// did the plug-in have a dropmodels child element?
		DropmodelType dt = plugin.getDropmodels();
		if (dt != null) 
			processDropmodelStmt(dt);

		// get the traces when dealing with IModifiyingTool
		if (tool instanceof IModifyingTool) {
			List<MarkedTrace> foo = ((IModifyingTool) tool).getMarkedTraces();
			if (foo != null)
				this.m_MarkedTraces.addAll(foo);
		}
		
	}
	
	/**
	 * process a Subchain statement in the toolchain
	 * 
	 * @param chain
	 * @param monitor
	 * @return true/false, depending on whether subchain could be successfully processed
	 */
	private final boolean processSubchain(SubchainType chain,
			IProgressMonitor monitor) {
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
			PluginConnector foo = m_OpenPlugins.get(firstplugin);
			if (foo != null) {
				changes = foo.hasPerformedChanges();
			} else changes = false;
			
			// iterate over subchain until break
			// caused by first plugin
			while (true) {

				for (Object o : chain.getPluginOrSubchain()) {
					if (monitor.isCanceled() || this.m_ToolchainCancelRequest) {
						this.m_ToolchainCancelRequest = true;
						return false;
					}
					if (o instanceof PluginType) {
						PluginType plugin = (PluginType) o;
						processPlugin(plugin);
						progress.worked(1);
						work_remain--;
						progress.setWorkRemaining(work_remain);
					} else if (o instanceof SubchainType) {
						SubchainType subchain = (SubchainType) o;
						// if chain has at least one plugin
						// return type of other Subchains is irrelevant
						processSubchain(subchain, progress
								.newChild(1));
						progress.worked(1);
						work_remain--;
						progress.setWorkRemaining(work_remain);
					} else {
						continue;
					}
				}

				foo = m_OpenPlugins.get(firstplugin);
				boolean bar;
				if (foo != null) bar = foo.hasPerformedChanges();
				else bar = false;

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
					if (monitor.isCanceled() || this.m_ToolchainCancelRequest) {
						this.m_ToolchainCancelRequest = true;
						return false;
					}
					if (o instanceof SubchainType) {
						SubchainType subchain = (SubchainType) o;
						boolean foo = processSubchain(subchain,
								progress.newChild(1));
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
	 * @param st
	 */
	private final void processSerializeStmt(SerializeType st) {
		ArrayList<GraphType> model_list = new ArrayList<GraphType>();
		GraphType g = null;
		if (st.getParser() != null) {
			g = this.m_ModelManager.getGraphTypeByGeneratorPluginId(this.m_Core.getParser().getPluginID());
			if (g != null)
				model_list.add(g);
			else {
				s_Logger.warn("Parser model could not be found!");
			}
		}
		for (ModelType m : st.getModel()) {
			if (m.getId().equals("mostrecent")) {
				g = this.m_ModelManager.getLastAdded();
			} else {
				g = this.m_ModelManager.getGraphTypeByGeneratorPluginId(m.getId());
			}
			if (g != null)
				model_list.add(g);
			else 
				s_Logger.warn("Model " + m.getId() + " could not be found!");
		}
		for (GraphType gt: model_list) {
			try {
				s_Logger.debug("Attempting to serialize model " + gt.toString() + " ...");
				this.m_ModelManager.persistAndDropExistingGraph(gt);
				s_Logger.debug("Persisting model succeeded.");
			} catch (StoreObjectException e) {
				s_Logger.error(
						"An error occurred while persisting selected model", e);
			} catch (GraphNotFoundException e) {
				s_Logger.error("Specified graph could not be found.", e);
			}

		}
	}

	/**
	 * process a serialize statement in toolchain
	 * 
	 * @param dt
	 */
	private final void processDropmodelStmt(DropmodelType dt) {		
		if (dt.getParser() != null) {
			GraphType g = null;
			g = this.m_ModelManager.getGraphTypeByGeneratorPluginId(this.m_Core.getParser().getPluginID());
			s_Logger.debug("Attempting to drop parser model...");
			if (g != null) {
				boolean success = this.m_ModelManager.removeItem(g);
			
			if (success)
				s_Logger.info("Dropping  model succeeded.");
			else 
				s_Logger.warn("Failed to remove parser model.");
			}
		}
		
		for (ModelIdOnlyType m : dt.getModel()) {
			GraphType g = null;
			g = this.m_ModelManager.getGraphTypeByGeneratorPluginId(m.getId());
			s_Logger.debug("Attempting to drop model " + m.getId() + " ...");
			if (g == null) {
				s_Logger.warn("Tried to remove a model that did not exist: " + m.getId() + ".");
				continue;
			}
			
			boolean success = this.m_ModelManager.removeItem(g);
			
			if (success)

				s_Logger.info("Dropping  model succeeded.");
			else 
				s_Logger.warn("Failed to remove model " + m.getId() + ".");
			
		}
	}
	
	public void reset() {
		this.m_OpenPlugins.clear();
		this.m_MarkedTraces.clear();
		this.m_ToolchainCancelRequest = false;
	}
	
	
	public HashMap<String, PluginConnector> getOpenPlugins() {
		return this.m_OpenPlugins;
	}
	
}
