/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2013-2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 * 
 * This file is part of the ULTIMATE BuchiProgramProduct plug-in.
 * 
 * The ULTIMATE BuchiProgramProduct plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiProgramProduct plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiProgramProduct plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiProgramProduct plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiProgramProduct plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.buchiprogramproduct;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
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
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.productgenerator.ProductGenerator;
import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ltl2aut.never2nwa.NWAContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class BuchiProductObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private RootNode mRcfg;
	private NWAContainer mNeverClaimNWAContainer;
	private RootNode mProduct;
	private final IUltimateServiceProvider mServices;
	private final ProductBacktranslator mBacktranslator;
	private final IToolchainStorage mStorage;

	public BuchiProductObserver(final ILogger logger, final IUltimateServiceProvider services, final ProductBacktranslator backtranslator, final IToolchainStorage storage) {
		mLogger = logger;
		mServices = services;
		mStorage = storage;
		mRcfg = null;
		mProduct = null;
		mNeverClaimNWAContainer = null;
		mBacktranslator = backtranslator;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {

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
		final IPreferenceProvider ups = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		try {
			final LTLPropertyCheck ltlAnnot = LTLPropertyCheck.getAnnotation(mNeverClaimNWAContainer);
			mProduct = new ProductGenerator(mNeverClaimNWAContainer.getNWA(), mRcfg, ltlAnnot, mServices,
					mBacktranslator).getProductRcfg();
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
				continueOptimization = optimizeRemoveSinkStates(ups, continueOptimization);
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

		} catch (final Exception e) {
			mLogger.error(String.format(
					"BuchiProgramProduct encountered an error during product automaton generation:\n %s", e));
			throw e;
		}
	}

	private boolean optimizeRemoveSinkStates(final IPreferenceProvider ups, boolean continueOptimization) {
		if (ups.getBoolean(PreferenceInitializer.OPTIMIZE_REMOVE_SINK_STATES)) {
			final RemoveSinkStates rss = new RemoveSinkStates(mProduct, mServices, mStorage);
			mProduct = rss.getResult();
			continueOptimization = continueOptimization || rss.isGraphChanged();
		}
		return continueOptimization;
	}

	private boolean optimizeRemoveInfeasibleEdges(final IPreferenceProvider ups, boolean continueOptimization) {
		if (ups.getBoolean(PreferenceInitializer.OPTIMIZE_REMOVE_INFEASIBLE_EDGES)) {
			final RemoveInfeasibleEdges opt1 = new RemoveInfeasibleEdges(mProduct, mServices, mStorage);
			mProduct = opt1.getResult();
			continueOptimization = continueOptimization || opt1.isGraphChanged();
		}
		return continueOptimization;
	}

	private boolean optimizeMaximizeFinalStates(final IPreferenceProvider ups, boolean continueOptimization) {
		if (ups.getBoolean(PreferenceInitializer.OPTIMIZE_MAXIMIZE_FINAL_STATES)) {
			final MaximizeFinalStates opt2 = new MaximizeFinalStates(mProduct, mServices, mStorage);
			mProduct = opt2.getResult();
			continueOptimization = continueOptimization || opt2.isGraphChanged();
		}
		return continueOptimization;
	}

	private boolean optimizeMinimizeStates(final IPreferenceProvider ups, boolean continueOptimization) {
		final MinimizeStates minimizeStates = ups.getEnum(PreferenceInitializer.OPTIMIZE_MINIMIZE_STATES,
				MinimizeStates.class);

		if (minimizeStates != MinimizeStates.NONE) {
			BaseProductOptimizer opt3;
			switch (minimizeStates) {
			case SINGLE:
				opt3 = new MinimizeStatesSingleEdgeSingleNode(mProduct, mServices, mStorage);
				break;
			case SINGLE_NODE_MULTI_EDGE:
				opt3 = new MinimizeStatesMultiEdgeSingleNode(mProduct, mServices, mStorage);
				break;
			case MULTI:
				opt3 = new MinimizeStatesMultiEdgeMultiNode(mProduct, mServices, mStorage);
				break;
			default:
				throw new IllegalArgumentException(minimizeStates + " is an unknown enum value!");

			}
			mProduct = opt3.getResult();
			continueOptimization = continueOptimization || opt3.isGraphChanged();
		}
		return continueOptimization;
	}

	private boolean optimizeSimplifyAssumes(final IPreferenceProvider ups, boolean continueOptimization) {
		if (ups.getBoolean(PreferenceInitializer.OPTIMIZE_SIMPLIFY_ASSUMES)) {
			final BaseProductOptimizer opt4 = new AssumeMerger(mProduct, mServices, mStorage);
			mProduct = opt4.getResult();
			continueOptimization = continueOptimization || opt4.isGraphChanged();
		}
		return continueOptimization;
	}

	private void reportSizeBenchmark(final String message, final INestedWordAutomaton<CodeBlock, String> nwa) {
		reportSizeBenchmark(message, new SizeBenchmark(nwa, message));
	}

	private void reportSizeBenchmark(final String message, final RootNode root) {
		reportSizeBenchmark(message, new SizeBenchmark(root, message));
	}

	private void reportSizeBenchmark(final String message, final SizeBenchmark bench) {
		mLogger.info(message + " " + bench);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new BenchmarkResult<>(Activator.PLUGIN_ID, message, bench));
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
	public boolean process(final IElement root) throws Exception {

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
