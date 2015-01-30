package de.uni_freiburg.informatik.ultimate.buchiprogramproduct;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct.MaximizeFinalStates;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct.MinimizeLinearStates;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct.RemoveInfeasibleEdges;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ltl2aut.never2nwa.NWAContainer;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.result.LTLPropertyCheck;

public class BuchiProductObserver implements IUnmanagedObserver {

	private final Logger mLogger;
	private RootNode mRcfg;
	private NWAContainer mNeverClaimNWAContainer;
	private RootNode mProduct;
	private final IUltimateServiceProvider mServices;
	private final ProductBacktranslator mBacktranslator;

	public BuchiProductObserver(Logger logger, IUltimateServiceProvider services, ProductBacktranslator backtranslator) {
		mLogger = logger;
		mServices = services;
		mRcfg = null;
		mProduct = null;
		mNeverClaimNWAContainer = null;
		mBacktranslator = backtranslator;
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

		try {
			LTLPropertyCheck ltlAnnot = LTLPropertyCheck.getAnnotation(mNeverClaimNWAContainer);
			mProduct = new ProductGenerator(mNeverClaimNWAContainer.getNWA(), mRcfg, ltlAnnot, mServices,
					mBacktranslator).getProductRCFG();
			mLogger.info("Finished generation of product automaton successfully");

			boolean optimize = true;
			while (optimize) {
				RemoveInfeasibleEdges opt1 = new RemoveInfeasibleEdges(mProduct, mServices);
				mProduct = opt1.getResult();
				MaximizeFinalStates opt2 = new MaximizeFinalStates(mProduct, mServices);
				mProduct = opt2.getResult();
				MinimizeLinearStates opt3 = new MinimizeLinearStates(mProduct, mServices);
				mProduct = opt3.getResult();

				optimize = opt1.IsGraphChanged() || opt2.IsGraphChanged() || opt3.IsGraphChanged();
			}

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

	public IElement getModel() {
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
