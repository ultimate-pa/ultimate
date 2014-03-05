package de.uni_freiburg.informatik.ultimate.BuchiProgramProduct;

import org.apache.log4j.Logger;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.NeverStatement;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class BuchiProductObserver implements IUnmanagedObserver {

	private Logger mLogger;
	private RootNode mRcfg;
	private AstNode mNeverClaim;
	private Product mProduct;

	public BuchiProductObserver() {
		mLogger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
		mRcfg = null;
		mProduct = null;
		mNeverClaim = null;
	}

	@Override
	public void init() {

	}

	@Override
	public void finish() throws Throwable {
		if (mNeverClaim == null || mRcfg == null) {
			return;
		}

		BoogieSymbolTable symbolTable = PreprocessorAnnotation.getAnnotation(mRcfg).getSymbolTable();

		NestedWordAutomaton<BoogieASTNode, String> nwa;

		mLogger.debug("Transforming NeverClaim to NestedWordAutomaton...");
		try {
			// Build NWA from LTL formula in NeverClaim representation
			nwa = new Never2Automaton(mNeverClaim, symbolTable).getAutomaton();
			if (nwa == null) {
				throw new NullPointerException("nwa is null");
			}
		} catch (Exception e) {
			mLogger.error(String
					.format("BuchiProgramProduct encountered an error during NeverClaim to NestedWordAutomaton transformation:\n %s",
							e));
			throw e;
		}

		mLogger.debug("Beginning generation of product automaton...");

		try {
			mProduct = new Product(nwa, mRcfg);
		} catch (Exception e) {
			mLogger.error(String.format(
					"BuchiProgramProduct encountered an error during product automaton generation:\n %s", e));
			throw e;
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
	 * Collect one RCFG and one LTL2Aut.AST
	 */
	public boolean process(IElement root) throws Exception {

		// collect root nodes of Buechi automaton
		if (root instanceof NeverStatement) {
			mLogger.debug("Collecting NeverClaim");
			mNeverClaim = ((AstNode) root);
			return false;
		}

		// collect root node of program's RCFG
		if (root instanceof RootNode) {
			mLogger.debug("Collecting RCFG RootNode");
			mRcfg = ((RootNode) root);
			return false;
		}

		return true;

	}

}
