/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.LTLFiniteCounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.LTLInfiniteCounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.NonTerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.NonterminatingLassoResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult.TERMINATION;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lassoranker.BacktranslationUtil;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class BuchiAutomizerObserver implements IUnmanagedObserver {

	private IElement mGraphRoot;
	private SmtManager mSmtManager;
	private TAPreferences mPref;

	private RootAnnot mRootAnnot;
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mStorage;

	public BuchiAutomizerObserver(final IUltimateServiceProvider services, final IToolchainStorage storage) {
		mServices = services;
		mStorage = storage;
	}

	@Override
	public boolean process(final IElement root) throws IOException {
		if (!(root instanceof RootNode)) {
			return false;
		}
		mRootAnnot = ((RootNode) root).getRootAnnot();
		final TAPreferences taPrefs = new TAPreferences(mServices);
		mGraphRoot = root;

		mSmtManager = new SmtManager(mRootAnnot.getScript(), mRootAnnot.getBoogie2SMT(),
				mRootAnnot.getModGlobVarManager(), mServices, false, mRootAnnot.getManagedScript(),
				taPrefs.getSimplificationTechnique(), taPrefs.getXnfConversionTechnique());

		mPref = taPrefs;

		final BuchiCegarLoop bcl = new BuchiCegarLoop((RootNode) root, mSmtManager, mPref, mServices, mStorage);
		final Result result = bcl.iterate();
		final BuchiCegarLoopBenchmarkGenerator benchGen = bcl.getBenchmarkGenerator();
		benchGen.stop(CegarLoopStatisticsDefinitions.OverallTime.toString());

		final IResult benchDecomp = new BenchmarkResult<String>(Activator.PLUGIN_ID, "Constructed decomposition of program",
				bcl.getMDBenchmark());
		reportResult(benchDecomp);

		final boolean constructTermcompProof = (mServices.getPreferenceProvider(Activator.PLUGIN_ID))
				.getBoolean(PreferenceInitializer.LABEL_TermcompProof);
		if (constructTermcompProof) {
			final IResult termcompProof = new BenchmarkResult<Double>(Activator.PLUGIN_ID,
					"Constructed termination proof in form of nested word automata", bcl.getTermcompProofBenchmark());
			reportResult(termcompProof);
		}

		final BuchiAutomizerTimingBenchmark timingBenchmark = new BuchiAutomizerTimingBenchmark(benchGen);
		final IResult benchTiming = new BenchmarkResult<>(Activator.PLUGIN_ID, "Timing statistics", timingBenchmark);
		reportResult(benchTiming);

		interpretAndReportResult(bcl, result);
		return false;
	}

	/**
	 * Report a nontermination argument back to Ultimate's toolchain
	 */
	private void reportNonTerminationResult(final ProgramPoint honda, final NonTerminationArgument nta) {
		// TODO: translate also the rational coefficients to Expressions?
		// mRootAnnot.getBoogie2Smt().translate(term)
		final Term2Expression term2expression = mRootAnnot.getBoogie2SMT().getTerm2Expression();

		final List<Map<IProgramVar, Rational>> states = new ArrayList<Map<IProgramVar, Rational>>();
		states.add(nta.getStateInit());
		states.add(nta.getStateHonda());
		states.addAll(nta.getGEVs());
		final List<Map<Expression, Rational>> initHondaRays = BacktranslationUtil.rank2Boogie(term2expression, states);

		final NonTerminationArgumentResult<RcfgElement, Expression> result = new NonTerminationArgumentResult<RcfgElement, Expression>(
				honda, Activator.PLUGIN_NAME, initHondaRays.get(0), initHondaRays.get(1),
				initHondaRays.subList(2, initHondaRays.size()), nta.getLambdas(), nta.getNus(),
				getBacktranslationService(), Expression.class);
		reportResult(result);
	}

	private void interpretAndReportResult(final BuchiCegarLoop bcl, final Result result) throws AssertionError {
		String whatToProve = "termination";

		if (bcl.isInLTLMode()) {
			final LTLPropertyCheck ltlAnnot = LTLPropertyCheck.getAnnotation(mGraphRoot);
			switch (result) {
			case NONTERMINATING:
				// there is a violation of the LTL property
				reportLTLPropertyIsViolated(bcl, ltlAnnot);
				return;
			case TERMINATING:
				// the LTL property holds
				reportLTLPropertyHolds(bcl, ltlAnnot);
				return;
			case TIMEOUT:
			case UNKNOWN:
				// use the standard report, but say its the LTL property
				whatToProve = ltlAnnot.getLTLProperty();
				break;
			default:
				throw new AssertionError("Extend the switch with the new enum member " + result);
			}
		}

		if (result == Result.TERMINATING) {
			final String longDescr = "Buchi Automizer proved that your program is terminating";
			final IResult reportRes = new TerminationAnalysisResult(Activator.PLUGIN_ID, TERMINATION.TERMINATING,
					longDescr);
			reportResult(reportRes);
		} else if (result == Result.UNKNOWN) {
			final NestedLassoRun<CodeBlock, IPredicate> counterexample = bcl.getCounterexample();
			final StringBuilder longDescr = new StringBuilder();
			longDescr.append("Buchi Automizer is unable to decide " + whatToProve + " for the following lasso. ");
			longDescr.append(System.getProperty("line.separator"));
			longDescr.append("Stem: ");
			longDescr.append(counterexample.getStem().getWord());
			longDescr.append(System.getProperty("line.separator"));
			longDescr.append("Loop: ");
			longDescr.append(counterexample.getLoop().getWord());
			final IResult reportRes = new TerminationAnalysisResult(Activator.PLUGIN_ID, TERMINATION.UNKNOWN,
					longDescr.toString());
			reportResult(reportRes);
		} else if (result == Result.TIMEOUT) {
			final ProgramPoint position = mRootAnnot.getEntryNodes().values().iterator().next();
			final String longDescr = "Timeout while trying to prove " + whatToProve + ". "
					+ bcl.getToolchainCancelledException().prettyPrint();
			final IResult reportRes = new TimeoutResultAtElement<RcfgElement>(position, Activator.PLUGIN_ID,
					mServices.getBacktranslationService(), longDescr);
			reportResult(reportRes);
		} else if (result == Result.NONTERMINATING) {
			final String longDescr = "Buchi Automizer proved that your program is nonterminating for some inputs";
			final IResult reportRes = new TerminationAnalysisResult(Activator.PLUGIN_ID, TERMINATION.NONTERMINATING,
					longDescr);
			reportResult(reportRes);

			final NestedLassoRun<CodeBlock, IPredicate> counterexample = bcl.getCounterexample();
			final IPredicate hondaPredicate = counterexample.getLoop().getStateAtPosition(0);
			final ProgramPoint honda = ((ISLPredicate) hondaPredicate).getProgramPoint();
			final NonTerminationArgument nta = bcl.getNonTerminationArgument();
			reportNonTerminationResult(honda, nta);
			reportResult(new BenchmarkResult<String>(Activator.PLUGIN_NAME, "NonterminationBenchmark",
					new NonterminationBenchmark(nta)));

			final Map<Integer, ProgramState<Term>> partialProgramStateMapping = Collections.emptyMap();
			@SuppressWarnings("unchecked")
			final
			RcfgProgramExecution stemPE = new RcfgProgramExecution(counterexample.getStem().getWord().asList(),
					partialProgramStateMapping, new Map[counterexample.getStem().getLength()]);
			@SuppressWarnings("unchecked")
			final
			RcfgProgramExecution loopPE = new RcfgProgramExecution(counterexample.getLoop().getWord().asList(),
					partialProgramStateMapping, new Map[counterexample.getLoop().getLength()]);
			final IResult ntreportRes = new NonterminatingLassoResult<RcfgElement, RCFGEdge, Term>(honda,
					Activator.PLUGIN_ID, mServices.getBacktranslationService(), stemPE, loopPE,
					honda.getPayload().getLocation());
			reportResult(ntreportRes);
		} else {
			throw new AssertionError();
		}
	}

	private void reportLTLPropertyHolds(final BuchiCegarLoop bcl, final LTLPropertyCheck ltlAnnot) {
		final IResult result = new AllSpecificationsHoldResult(Activator.PLUGIN_ID,
				"Buchi Automizer proved that the LTL property " + ltlAnnot.getLTLProperty() + " holds");
		reportResult(result);
	}

	private void reportLTLPropertyIsViolated(final BuchiCegarLoop bcl, final LTLPropertyCheck ltlAnnot) {
		final NestedLassoRun<CodeBlock, IPredicate> counterexample = bcl.getCounterexample();
		final ProgramPoint position = ((ISLPredicate) counterexample.getLoop().getStateAtPosition(0)).getProgramPoint();
		// first, check if the counter example is really infinite or not

		final List<CodeBlock> stem = counterexample.getStem().getWord().asList();
		final List<CodeBlock> loop = counterexample.getLoop().getWord().asList();

		final boolean isFinite = isLTLCounterExampleFinite(loop);

		if (isFinite) {
			// TODO: Make some attempt at getting the values
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping = Collections.emptyMap();
			final List<CodeBlock> combined = new ArrayList<CodeBlock>();
			combined.addAll(stem);

			// TODO: It seems that the loop is not necessary if the trace is
			// finite, but only contains things that have been inserted by
			// BuchiProgramProduct
			// combined.addAll(loop);

			@SuppressWarnings("unchecked")
			final
			RcfgProgramExecution cex = new RcfgProgramExecution(combined, partialProgramStateMapping,
					new Map[combined.size()]);
			reportResult(new LTLFiniteCounterExampleResult<>(position, Activator.PLUGIN_ID,
					mServices.getBacktranslationService(), cex, ltlAnnot));
		} else {
			// TODO: Make some attempt at getting the values
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping = Collections.emptyMap();

			@SuppressWarnings("unchecked")
			final
			RcfgProgramExecution stemPE = new RcfgProgramExecution(stem, partialProgramStateMapping,
					new Map[stem.size()]);
			@SuppressWarnings("unchecked")
			final
			RcfgProgramExecution loopPE = new RcfgProgramExecution(loop, partialProgramStateMapping,
					new Map[loop.size()]);
			reportResult(new LTLInfiniteCounterExampleResult<RcfgElement, RCFGEdge, Term>(position, Activator.PLUGIN_ID,
					mServices.getBacktranslationService(), stemPE, loopPE, position.getPayload().getLocation(),
					ltlAnnot.getLTLProperty()));
		}
	}

	private boolean isLTLCounterExampleFinite(final List<CodeBlock> loop) {
		// TODO: does not work reliably
		// boolean isFinite = true;
		//
		// // is the loop a real loop in the program?
		// for (CodeBlock cb : loop) {
		// if (mRootAnnot.getLoopLocations().keySet().contains(cb.getSource()))
		// {
		// isFinite = false;
		// }
		// }
		//
		// // TODO: is the loop part of a recursion? Then its also not finite
		//
		// return isFinite;
		return false;
	}

	/**
	 * @return the current translator sequence for building results
	 */
	private IBacktranslationService getBacktranslationService() {
		return mServices.getBacktranslationService();
	}

	void reportResult(final IResult res) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, res);
	}

	@Override
	public void finish() {

	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {

	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	public IElement getModel() {
		return mGraphRoot;
	}

	// public static TransFormula sequentialComposition(int serialNumber,
	// Boogie2SMT boogie2smt, TransFormula... transFormulas) {
	// TransFormula result = transFormulas[0];
	// for (int i=1; i<transFormulas.length; i++) {
	// result = TransFormula.sequentialComposition(result, transFormulas[i],
	// boogie2smt, serialNumber++);
	// }
	// return result;
	// }

	private class NonterminationBenchmark implements ICsvProviderProvider<String> {
		private final String mNtar;
		private final boolean mLambdaZero;
		private final boolean mGEVZero;

		public NonterminationBenchmark(final NonTerminationArgument nta) {
			boolean lambdaZero = true;
			boolean gevZero = true;
			final List<Rational> lambdas = nta.getLambdas();
			for (int i = 0; i < nta.getNumberOfGEVs(); ++i) {
				lambdaZero &= (nta.getLambdas().get(i).numerator().equals(BigInteger.ZERO));
				gevZero &= isZero(nta.getGEVs().get(i));
			}

			mLambdaZero = lambdaZero;
			mGEVZero = gevZero;
			mNtar = (isFixpoint() ? "Fixpoint " : "Unbounded Execution ") + "Lambdas: " + lambdas + " GEVs: "
					+ (mGEVZero ? "is zero" : "is not zero");
		}

		private boolean isFixpoint() {
			return mLambdaZero || mGEVZero;
		}

		/**
		 * Return true iff all coefficients of generalized eigenvector are zero.
		 */
		private boolean isZero(final Map<IProgramVar, Rational> gev) {
			for (final Entry<IProgramVar, Rational> entry : gev.entrySet()) {
				if (!entry.getValue().numerator().equals(BigInteger.ZERO)) {
					return false;
				}
			}
			return true;
		}

		@Override
		public ICsvProvider<String> createCvsProvider() {
			return new SimpleCsvProvider<>(Arrays.asList(new String[] { "nta" }));
		}

		@Override
		public String toString() {
			return mNtar;
		}

	}

}
