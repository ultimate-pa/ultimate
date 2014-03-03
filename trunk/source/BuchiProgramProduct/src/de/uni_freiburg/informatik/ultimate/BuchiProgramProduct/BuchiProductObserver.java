package de.uni_freiburg.informatik.ultimate.BuchiProgramProduct;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.NeverStatement;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class BuchiProductObserver implements IUnmanagedObserver {

	private NestedWordAutomaton<BoogieASTNode, String> mAutomaton;
	private RootNode mRcfg;

	private Product mProduct;
	private Logger mLogger;

	public BuchiProductObserver() {
		mAutomaton = null;
		mRcfg = null;
		mProduct = null;
		mLogger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init() {
	}

	@Override
	public void finish() throws Throwable 
	{
		// if everything is found, execute produrct
		if (mAutomaton != null && mRcfg != null) {
			mLogger.debug("Beginning generation of product automation...");

			try {
				mProduct = new Product(mAutomaton, mRcfg);
			} catch (Exception e) {
				mLogger.error(String.format("BuchiProgramProduct encountered an error during product generation:\n %s",
						e));
				throw e;
			}
		}
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	public Product getProduct() {
		return mProduct;
	}

	@Override
	/**
	 * Collect one RCFG and one LTL2Aut.AST and execute the product 
	 * algorithm on them.
	 */
	public boolean process(IElement root) throws Exception {

		// collect root nodes of Buechi automaton
		if (root instanceof NeverStatement && this.mAutomaton == null) {
			mLogger.debug("Transforming NeverClaim to NestedWordAutomation...");
			// build and get automaton
			try {
				mAutomaton = new Never2Automaton((AstNode) root).getAutomaton();
			} catch (Exception e) {
				mLogger.error(String.format(
						"BuchiProgramProduct encountered an error during neverclaim to Buchi transformation:\n %s", e));
				throw e;
			}
			return false;
		}

		// collect root node of program's RCFG
		if (root instanceof RootNode && this.mRcfg == null) {
			mLogger.debug("Saving RCFG RootNode...");
			mRcfg = ((RootNode) root);
			return false;
		}

		return true;

	}

}
