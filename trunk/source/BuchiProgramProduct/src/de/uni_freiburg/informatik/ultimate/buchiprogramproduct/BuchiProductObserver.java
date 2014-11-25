package de.uni_freiburg.informatik.ultimate.buchiprogramproduct;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ltl2aut.never2nwa.NWAContainer;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.result.LTLPropertyCheck;

public class BuchiProductObserver implements IUnmanagedObserver {

	private final Logger mLogger;
	private RootNode mRcfg;
	private NWAContainer mNeverClaimNWAContainer;
	private Product mProduct;
	private final IUltimateServiceProvider mServices;

	public BuchiProductObserver(Logger logger, IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
		mRcfg = null;
		mProduct = null;
		mNeverClaimNWAContainer = null;
	}

	@Override
	public void init() {

	}

	@Override
	public void finish() throws Throwable {
		if (mNeverClaimNWAContainer == null || mRcfg == null) {
			return;
		}

		mLogger.info("Beginning generation of product automaton");
		ProductBacktranslator translator = new ProductBacktranslator(CodeBlock.class, Expression.class);
		mServices.getBacktranslationService().addTranslator(translator);

		try {
			LTLPropertyCheck ltlAnnot = LTLPropertyCheck.getAnnotation(mNeverClaimNWAContainer);
			mProduct = new Product(mNeverClaimNWAContainer.getNWA(), mRcfg, ltlAnnot, mServices, translator);
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
		if (root instanceof NWAContainer) {
			mLogger.debug("Collecting NWA representing NeverClaim");
			mNeverClaimNWAContainer = ((NWAContainer) root);
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
