package local.stalin.plugins.generator.rcfgbuilder;
import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IElement;
import local.stalin.model.INode;
import local.stalin.model.boogie.ast.Unit;
import local.stalin.model.boogie.ast.wrapper.WrapperNode;
import local.stalin.plugins.generator.rcfgbuilder.preferences.PreferenceValues;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class RCFGBuilderObserver implements IUnmanagedObserver {

	/**
	 * If true an InternalTransition represents a whole block, otherwise there
	 * is an InternalTransition for every single Statement.
	 */
	public static boolean MULTIPLE_STATEMENTS_PER_TRANSITION;
	
	/**
     * Root Node of this Stalin model. I use this to store information that
     * should be passed to the next plugin. The Sucessors of this node exactly
     * the initial nodes of procedures.
	 */
	private static RootNode m_graphroot;
	
	/**
	 * Logger for this plugin.
	 */
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	/**
	 * 
	 * @return the root of the CFG.
	 */
	public INode getRoot(){
		return RCFGBuilderObserver.m_graphroot;
	}
	
	/**
	 * Copied from CFG Builder
	 * 
	 * Called by the Stalin Framework. Finds all procedure declarations and
	 * checks whether they're implementations or just declarations. If
	 * implementation is present calls makeProcedureCFG() and appends CFG as
	 * child of procedure node to CFG
	 */
	public boolean process(IElement root) {
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode(Activator.PLUGIN_ID);
		boolean multipleStatementsPerTransition = 
			prefs.getBoolean(PreferenceValues.NAME_MULTIPLE_STATEMENTS, 
							 PreferenceValues.DEF_MULTIPLE_STATEMENTS);
		MULTIPLE_STATEMENTS_PER_TRANSITION = multipleStatementsPerTransition;
		
		
		if (!(root instanceof WrapperNode)) {
			//TODO
			s_Logger.debug("No WrapperNode. Let STALIN process with next node");
			return true;
		}
		else {
			Unit unit = (Unit) ((WrapperNode)root).getBacking();
			RecursiveCFGBuilder recCFGBuilder = 
				new RecursiveCFGBuilder(multipleStatementsPerTransition);
			m_graphroot = recCFGBuilder.getRootNode(unit);
		}
		return false;
	}
	
	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

}
