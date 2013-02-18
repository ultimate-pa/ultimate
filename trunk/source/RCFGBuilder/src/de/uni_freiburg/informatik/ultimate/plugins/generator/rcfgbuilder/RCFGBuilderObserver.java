package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.WrapperNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

import org.apache.log4j.Logger;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class RCFGBuilderObserver implements IUnmanagedObserver {

	/**
     * Root Node of this Ultimate model. I use this to store information that
     * should be passed to the next plugin. The Sucessors of this node exactly
     * the initial nodes of procedures.
	 */
	private static RootNode m_graphroot;
	
	/**
	 * Logger for this plugin.
	 */
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	/**
	 * 
	 * @return the root of the CFG.
	 */
	public RootNode getRoot(){
		return RCFGBuilderObserver.m_graphroot;
	}
	
	/**
	 * Copied from CFG Builder
	 * 
	 * Called by the Ultimate Framework. Finds all procedure declarations and
	 * checks whether they're implementations or just declarations. If
	 * implementation is present calls makeProcedureCFG() and appends CFG as
	 * child of procedure node to CFG
	 */
	public boolean process(IElement root) {
		if (!(root instanceof WrapperNode)) {
			//TODO
			s_Logger.debug("No WrapperNode. Let Ultimate process with next node");
			return true;
		}
		else {
			Unit unit = (Unit) ((WrapperNode)root).getBacking();
			Backtranslator translator =	new Backtranslator();
			CfgBuilder recCFGBuilder = new CfgBuilder(unit, translator);
			try {
				m_graphroot = recCFGBuilder.getRootNode(unit);
				UltimateServices.getInstance().getTranslatorSequence().add(translator);
			} catch (SMTLIBException e) {
				if (e.getMessage().equals("Cannot create quantifier in quantifier-free logic")) {
					s_Logger.warn("Unsupported syntax: " + e.getMessage());
				} else if (e.getMessage().equals("Sort Array not declared")) {
					s_Logger.warn("Unsupported syntax: " + e.getMessage());
				} else if (e.getMessage().equals("Unsupported non-linear arithmetic")) {
					s_Logger.warn("Unsupported syntax: " + e.getMessage());
				} else {
					throw e;
				}
			}
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
