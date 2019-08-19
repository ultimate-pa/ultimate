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
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.FixpointNonTerminationResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GeometricNonTerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.LTLFiniteCounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.LTLInfiniteCounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.NonTerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.NonterminatingLassoResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult.Termination;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType.Type;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lassoranker.BacktranslationUtil;
import de.uni_freiburg.informatik.ultimate.lassoranker.NonterminationArgumentStatistics;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.GeometricNonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.InfiniteFixpointRepetition;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessModelToAutomatonTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class BuchiAutomizerObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private final List<IIcfg<?>> mIcfgs;
	private IElement mRootOfNewModel;
	private WitnessNode mWitnessNode;
	private final List<AutomataTestFileAST> mAutomataTestFileAsts;
	private boolean mLastModel;
	private ModelType mCurrentGraphType;

	public BuchiAutomizerObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mLastModel = false;
		mIcfgs = new ArrayList<>();
		mAutomataTestFileAsts = new ArrayList<>();
	}

	@Override
	public boolean process(final IElement root) throws IOException {
		if (root instanceof IIcfg<?>) {
			mIcfgs.add((IIcfg<?>) root);
		}
		if (root instanceof WitnessNode && mCurrentGraphType.getType() == Type.VIOLATION_WITNESS) {
			if (mWitnessNode == null) {
				mWitnessNode = (WitnessNode) root;
			} else {
				throw new UnsupportedOperationException("two witness models");
			}
		}
		if (root instanceof AutomataTestFileAST) {
			mAutomataTestFileAsts.add((AutomataTestFileAST) root);
		}
		return false;
	}

	private IIcfg<?> doTerminationAnalysis(final IIcfg<?> icfg,
			final INestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) throws IOException, AssertionError {
		final TAPreferences taPrefs = new TAPreferences(mServices);

		final RankVarConstructor rankVarConstructor = new RankVarConstructor(icfg.getCfgSmtToolkit());
		final PredicateFactory predicateFactory =
				new PredicateFactory(mServices, icfg.getCfgSmtToolkit().getManagedScript(),
						rankVarConstructor.getCsToolkitWithRankVariables().getSymbolTable());

		final BuchiCegarLoop<?> bcl = new BuchiCegarLoop<>(icfg, icfg.getCfgSmtToolkit(), rankVarConstructor,
				predicateFactory, taPrefs, mServices, witnessAutomaton);
		final Result result = bcl.iterate();
		final BuchiCegarLoopBenchmarkGenerator benchGen = bcl.getBenchmarkGenerator();
		benchGen.stop(CegarLoopStatisticsDefinitions.OverallTime.toString());

		final IResult benchDecomp = new StatisticsResult<>(Activator.PLUGIN_ID, "Constructed decomposition of program",
				bcl.getMDBenchmark());
		reportResult(benchDecomp);

		final boolean constructTermcompProof = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_CONSTRUCT_TERMCOMP_PROOF);
		if (constructTermcompProof) {
			final IResult termcompProof = new StatisticsResult<>(Activator.PLUGIN_ID,
					"Constructed termination proof in form of nested word automata", bcl.getTermcompProofBenchmark());
			reportResult(termcompProof);
		}

		final BuchiAutomizerTimingBenchmark timingBenchmark = new BuchiAutomizerTimingBenchmark(benchGen);
		final IResult benchTiming = new StatisticsResult<>(Activator.PLUGIN_ID, "Timing statistics", timingBenchmark);
		reportResult(benchTiming);

		interpretAndReportResult(bcl, result, icfg);
		return icfg;
	}

	/**
	 * Report a nontermination argument back to Ultimate's toolchain
	 *
	 * @param nestedLassoWord
	 */
	private void reportNonTerminationResult(final IcfgLocation honda, final NonTerminationArgument nta,
			final NestedLassoWord<? extends IIcfgTransition<?>> nestedLassoWord) {
		final IcfgProgramExecution stemExecution =
				IcfgProgramExecution.create(nestedLassoWord.getStem().asList(), Collections.emptyMap());
		final IcfgProgramExecution loopExecution =
				IcfgProgramExecution.create(nestedLassoWord.getLoop().asList(), Collections.emptyMap());
		final NonTerminationArgumentResult<IIcfgTransition<IcfgLocation>, Term> result;
		final IcfgEdge honda1 = (IcfgEdge) nestedLassoWord.getLoop().getSymbol(0);
		if (nta instanceof GeometricNonTerminationArgument) {
			final GeometricNonTerminationArgument gnta = (GeometricNonTerminationArgument) nta;
			// TODO: translate also the rational coefficients to Expressions?
			// mRootAnnot.getBoogie2Smt().translate(term)
			// final Term2Expression term2expression = mIcfg.getBoogie2SMT().getTerm2Expression();

			final List<Map<IProgramVar, Rational>> states = new ArrayList<>();
			states.add(gnta.getStateInit());
			states.add(gnta.getStateHonda());
			states.addAll(gnta.getGEVs());
			final List<Map<Term, Rational>> initHondaRays = BacktranslationUtil.rank2Rcfg(states);

			result = new GeometricNonTerminationArgumentResult<>(honda1, Activator.PLUGIN_NAME, initHondaRays.get(0),
					initHondaRays.get(1), initHondaRays.subList(2, initHondaRays.size()), gnta.getLambdas(),
					gnta.getNus(), getBacktranslationService(), Term.class, stemExecution, loopExecution);
		} else if (nta instanceof InfiniteFixpointRepetition) {
			final InfiniteFixpointRepetition ifr = (InfiniteFixpointRepetition) nta;

			result = new FixpointNonTerminationResult<>(honda1, Activator.PLUGIN_NAME, ifr.getValuesAtInit(),
					ifr.getValuesAtHonda(), getBacktranslationService(), Term.class, stemExecution, loopExecution);
		} else {
			throw new IllegalArgumentException("unknown TerminationArgument");
		}
		reportResult(result);
	}

	private void interpretAndReportResult(final BuchiCegarLoop<?> bcl, final Result result, final IIcfg<?> icfg)
			throws AssertionError {
		String whatToProve = "termination";

		if (bcl.isInLTLMode()) {
			final LTLPropertyCheck ltlAnnot = LTLPropertyCheck.getAnnotation(icfg);
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
				whatToProve = ltlAnnot.getUltimateLTLProperty();
				break;
			default:
				throw new AssertionError("Extend the switch with the new enum member " + result);
			}
		}

		if (result == Result.TERMINATING) {
			final String longDescr = "Buchi Automizer proved that your program is terminating";
			final IResult reportRes =
					new TerminationAnalysisResult(Activator.PLUGIN_ID, Termination.TERMINATING, longDescr);
			reportResult(reportRes);
		} else if (result == Result.UNKNOWN) {
			final NestedLassoRun<?, IPredicate> counterexample = bcl.getCounterexample();
			final StringBuilder longDescr = new StringBuilder();
			longDescr.append("Buchi Automizer is unable to decide " + whatToProve + " for the following lasso. ");
			longDescr.append(System.getProperty("line.separator"));
			longDescr.append("Stem: ");
			longDescr.append(counterexample.getStem().getWord());
			longDescr.append(System.getProperty("line.separator"));
			longDescr.append("Loop: ");
			longDescr.append(counterexample.getLoop().getWord());
			final IResult reportRes =
					new TerminationAnalysisResult(Activator.PLUGIN_ID, Termination.UNKNOWN, longDescr.toString());
			reportResult(reportRes);
		} else if (result == Result.TIMEOUT) {
			final IcfgLocation position = icfg.getProcedureEntryNodes().values().iterator().next();
			final String longDescr = "Timeout while trying to prove " + whatToProve + ". "
					+ bcl.getToolchainCancelledException().printRunningTaskMessage();
			final IResult reportRes = new TimeoutResultAtElement<IIcfgElement>(position, Activator.PLUGIN_ID,
					mServices.getBacktranslationService(), longDescr);
			reportResult(reportRes);
		} else if (result == Result.NONTERMINATING) {
			final String longDescr = "Buchi Automizer proved that your program is nonterminating for some inputs";
			final IResult reportRes =
					new TerminationAnalysisResult(Activator.PLUGIN_ID, Termination.NONTERMINATING, longDescr);
			reportResult(reportRes);

			final NestedLassoRun<? extends IIcfgTransition<?>, IPredicate> counterexample = bcl.getCounterexample();
			final IPredicate hondaPredicate = counterexample.getLoop().getStateAtPosition(0);
			final IcfgLocation honda = ((ISLPredicate) hondaPredicate).getProgramPoint();
			final NonTerminationArgument nta = bcl.getNonTerminationArgument();
			reportNonTerminationResult(honda, nta, counterexample.getNestedLassoWord());
			reportResult(new StatisticsResult<>(Activator.PLUGIN_NAME,
					NonterminationArgumentStatistics.class.getSimpleName(), new NonterminationArgumentStatistics(nta)));

			final Map<Integer, ProgramState<Term>> partialProgramStateMapping = Collections.emptyMap();
			@SuppressWarnings("unchecked")
			final IcfgProgramExecution stemPE = IcfgProgramExecution.create(counterexample.getStem().getWord().asList(),
					partialProgramStateMapping, new Map[counterexample.getStem().getLength()]);
			@SuppressWarnings("unchecked")
			final IcfgProgramExecution loopPE = IcfgProgramExecution.create(counterexample.getLoop().getWord().asList(),
					partialProgramStateMapping, new Map[counterexample.getLoop().getLength()]);
			final IResult ntreportRes = new NonterminatingLassoResult<>(honda, Activator.PLUGIN_ID,
					mServices.getBacktranslationService(), stemPE, loopPE, ILocation.getAnnotation(honda));
			reportResult(ntreportRes);
		} else {
			throw new AssertionError();
		}
	}

	private void reportLTLPropertyHolds(final BuchiCegarLoop<?> bcl, final LTLPropertyCheck ltlAnnot) {
		final IResult result = new AllSpecificationsHoldResult(Activator.PLUGIN_ID,
				"Buchi Automizer proved that the LTL property " + ltlAnnot.getUltimateLTLProperty() + " holds");
		reportResult(result);
	}

	private void reportLTLPropertyIsViolated(final BuchiCegarLoop<?> bcl, final LTLPropertyCheck ltlAnnot) {
		final NestedLassoRun<? extends IIcfgTransition<?>, IPredicate> counterexample = bcl.getCounterexample();
		final IcfgLocation position = ((ISLPredicate) counterexample.getLoop().getStateAtPosition(0)).getProgramPoint();
		// first, check if the counter example is really infinite or not

		final List<? extends IIcfgTransition<?>> stem = counterexample.getStem().getWord().asList();
		final List<? extends IIcfgTransition<?>> loop = counterexample.getLoop().getWord().asList();

		final boolean isFinite = isLTLCounterExampleFinite(loop);

		if (isFinite) {
			// TODO: Make some attempt at getting the values
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping = Collections.emptyMap();
			final List<IIcfgTransition<?>> combined = new ArrayList<>();
			combined.addAll(stem);

			// TODO: It seems that the loop is not necessary if the trace is
			// finite, but only contains things that have been inserted by
			// BuchiProgramProduct
			// combined.addAll(loop);

			@SuppressWarnings("unchecked")
			final IcfgProgramExecution cex =
					IcfgProgramExecution.create(combined, partialProgramStateMapping, new Map[combined.size()]);
			reportResult(new LTLFiniteCounterExampleResult<>(position, Activator.PLUGIN_ID,
					mServices.getBacktranslationService(), cex, ltlAnnot));
		} else {
			// TODO: Make some attempt at getting the values
			final Map<Integer, ProgramState<Term>> partialProgramStateMapping = Collections.emptyMap();

			@SuppressWarnings("unchecked")
			final IcfgProgramExecution stemPE =
					IcfgProgramExecution.create(stem, partialProgramStateMapping, new Map[stem.size()]);
			@SuppressWarnings("unchecked")
			final IcfgProgramExecution loopPE =
					IcfgProgramExecution.create(loop, partialProgramStateMapping, new Map[loop.size()]);
			reportResult(new LTLInfiniteCounterExampleResult<>(position, Activator.PLUGIN_ID,
					mServices.getBacktranslationService(), stemPE, loopPE, ILocation.getAnnotation(position),
					ltlAnnot.getUltimateLTLProperty()));
		}
	}

	private boolean isLTLCounterExampleFinite(final List<?> loop) {
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
	public void finish() throws IOException {
		if (mLastModel) {
			@SuppressWarnings("unchecked")
			final IIcfg<IcfgLocation> rcfgRootNode = (IIcfg<IcfgLocation>) mIcfgs.stream()
					.filter(a -> IcfgLocation.class.isAssignableFrom(a.getLocationClass())).reduce((a, b) -> b)
					.orElseThrow(UnsupportedOperationException::new);

			if (rcfgRootNode == null) {
				throw new UnsupportedOperationException("TraceAbstraction needs an RCFG");
			}
			mLogger.info("Analyzing ICFG " + rcfgRootNode.getIdentifier());
			INestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton;
			if (mWitnessNode == null) {
				witnessAutomaton = null;
			} else {
				mLogger.warn(
						"Found a witness automaton. I will only consider traces that are accepted by the witness automaton");
				witnessAutomaton = new WitnessModelToAutomatonTransformer(mWitnessNode, mServices).getResult();
			}
			mRootOfNewModel = doTerminationAnalysis(rcfgRootNode, witnessAutomaton);
		}
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		mCurrentGraphType = modelType;
		if (currentModelIndex == numberOfModels - 1) {
			mLastModel = true;
		}
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	public IElement getModel() {
		return mRootOfNewModel;
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

}
