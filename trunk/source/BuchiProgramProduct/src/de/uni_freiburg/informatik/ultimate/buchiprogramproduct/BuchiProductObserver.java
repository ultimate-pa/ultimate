package de.uni_freiburg.informatik.ultimate.buchiprogramproduct;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.NeverStatement;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot.BuchiProgramRootNodeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class BuchiProductObserver implements IUnmanagedObserver {

	private final Logger mLogger;
	private RootNode mRcfg;
	private AstNode mNeverClaim;
	private Product mProduct;
	private final IUltimateServiceProvider mServices;

	public BuchiProductObserver(Logger logger, IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
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
		ProductBacktranslator translator = new ProductBacktranslator(CodeBlock.class, Expression.class);
		mServices.getBacktranslationService().addTranslator(translator);

		mLogger.debug("Transforming NeverClaim to NestedWordAutomaton...");
		try {
			// Build NWA from LTL formula in NeverClaim representation
			nwa = new Never2Automaton(mNeverClaim, symbolTable, mLogger, mServices).getAutomaton();
			if (nwa == null) {
				throw new NullPointerException("nwa is null");
			}
		} catch (Exception e) {
			mLogger.error(String.format(
					"BuchiProgramProduct encountered an error during NeverClaim to NestedWordAutomaton"
							+ " transformation:\n %s", e));
			throw e;
		}

		mLogger.info("Beginning generation of product automaton");

		try {
			BuchiProgramRootNodeAnnotation ltlAnnot = BuchiProgramRootNodeAnnotation.getAnnotation(mNeverClaim);
			mProduct = new Product(nwa, mRcfg, ltlAnnot, mServices, translator);
			mLogger.info("Product automaton successfully generated");
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
