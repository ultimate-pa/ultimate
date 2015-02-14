package de.uni_freiburg.informatik.ultimate.buchiprogramproduct;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.benchmark.SizeBenchmark;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct.AssumeMerger;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct.BaseProductOptimizer;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct.MaximizeFinalStates;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct.MinimizeStatesMultiEdgeMultiNode;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct.MinimizeStatesMultiEdgeSingleNode;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct.MinimizeStatesSingleEdgeSingleNode;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct.RemoveInfeasibleEdges;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct.RemoveSinkStates;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.preferences.PreferenceInitializer.MinimizeStates;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ltl2aut.never2nwa.NWAContainer;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;

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

		// measure size of nwa and rcfg
		reportSizeBenchmark("Initial property automaton", mNeverClaimNWAContainer.getNWA());
		reportSizeBenchmark("Initial RCFG", mRcfg);
		
		mLogger.info("Beginning generation of product automaton");
		UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		try {
			LTLPropertyCheck ltlAnnot = LTLPropertyCheck.getAnnotation(mNeverClaimNWAContainer);
			mProduct = new ProductGenerator(mNeverClaimNWAContainer.getNWA(), mRcfg, ltlAnnot, mServices,
					mBacktranslator).getProductRCFG();
			mLogger.info("Finished generation of product automaton successfully");
			reportSizeBenchmark("Initial product", mProduct);

			int maxIters = ups.getInt(PreferenceInitializer.OPTIMIZE_MAX_ITERATIONS) - 1;
			if (maxIters < 0) {
				maxIters = -1;
			}
			int i = 1;
			while (true) {
				mLogger.debug("==== Optimization #" + i + "====");
				++i;
				boolean continueOptimization = false;

				continueOptimization = optimizeRemoveInfeasibleEdges(ups, continueOptimization);
				
				RemoveSinkStates rss = new RemoveSinkStates(mProduct,mServices);
				mProduct = rss.getResult();
				continueOptimization = continueOptimization || rss.IsGraphChanged();
				
				continueOptimization = optimizeMaximizeFinalStates(ups, continueOptimization);
				continueOptimization = optimizeMinimizeStates(ups, continueOptimization);
				continueOptimization = optimizeSimplifyAssumes(ups, continueOptimization);
				

				

				if (!mServices.getProgressMonitorService().continueProcessing()) {
					mServices.getResultService().reportResult(Activator.PLUGIN_ID,
							new TimeoutResult(Activator.PLUGIN_ID, "Timeout during product optimization"));
					return;
				}

				if (ups.getBoolean(PreferenceInitializer.OPTIMIZE_UNTIL_FIXPOINT) && continueOptimization
						&& maxIters != 0) {
					if (maxIters > 0) {
						maxIters--;
					}
					continue;
				}
				break;
			}
			reportSizeBenchmark("Optimized Product", mProduct);

		} catch (Exception e) {
			mLogger.error(String.format(
					"BuchiProgramProduct encountered an error during product automaton generation:\n %s", e));
			throw e;
		}
		return;
	}

	private boolean optimizeRemoveInfeasibleEdges(UltimatePreferenceStore ups, boolean continueOptimization) {
		if (ups.getBoolean(PreferenceInitializer.OPTIMIZE_REMOVE_INFEASIBLE_EDGES)) {
			RemoveInfeasibleEdges opt1 = new RemoveInfeasibleEdges(mProduct, mServices);
			mProduct = opt1.getResult();
			continueOptimization = continueOptimization || opt1.IsGraphChanged();
		}
		return continueOptimization;
	}

	private boolean optimizeMaximizeFinalStates(UltimatePreferenceStore ups, boolean continueOptimization) {
		if (ups.getBoolean(PreferenceInitializer.OPTIMIZE_MAXIMIZE_FINAL_STATES)) {
			MaximizeFinalStates opt2 = new MaximizeFinalStates(mProduct, mServices);
			mProduct = opt2.getResult();
			continueOptimization = continueOptimization || opt2.IsGraphChanged();
		}
		return continueOptimization;
	}

	private boolean optimizeMinimizeStates(UltimatePreferenceStore ups, boolean continueOptimization) {
		MinimizeStates minimizeStates = ups.getEnum(PreferenceInitializer.OPTIMIZE_MINIMIZE_STATES,
				MinimizeStates.class);

		if (minimizeStates != MinimizeStates.NONE) {
			BaseProductOptimizer opt3;
			switch (minimizeStates) {
			case SINGLE:
				opt3 = new MinimizeStatesSingleEdgeSingleNode(mProduct, mServices);
				break;
			case SINGLE_NODE_MULTI_EDGE:
				opt3 = new MinimizeStatesMultiEdgeSingleNode(mProduct, mServices);
				break;
			case MULTI:
				opt3 = new MinimizeStatesMultiEdgeMultiNode(mProduct, mServices);
				break;
			default:
				throw new IllegalArgumentException(minimizeStates + " is an unknown enum value!");

			}
			mProduct = opt3.getResult();
			continueOptimization = continueOptimization || opt3.IsGraphChanged();
		}
		return continueOptimization;
	}

	private boolean optimizeSimplifyAssumes(UltimatePreferenceStore ups, boolean continueOptimization) {
		if (ups.getBoolean(PreferenceInitializer.OPTIMIZE_SIMPLIFY_ASSUMES)) {
			BaseProductOptimizer opt4 = new AssumeMerger(mProduct, mServices);
			mProduct = opt4.getResult();
			continueOptimization = continueOptimization || opt4.IsGraphChanged();
		}
		return continueOptimization;
	}

	private void reportSizeBenchmark(String message, NestedWordAutomaton<CodeBlock, String> nwa) {
		reportSizeBenchmark(message, new SizeBenchmark(nwa, message));
	}

	private void reportSizeBenchmark(String message, RootNode root) {
		reportSizeBenchmark(message, new SizeBenchmark(root, message));
	}

	private void reportSizeBenchmark(String message, SizeBenchmark bench) {
		mLogger.info(message + " " + bench);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new BenchmarkResult<>(Activator.PLUGIN_ID, message, bench));
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
