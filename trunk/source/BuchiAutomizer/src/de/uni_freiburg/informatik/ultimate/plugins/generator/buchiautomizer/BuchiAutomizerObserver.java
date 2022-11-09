/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.FixpointNonTerminationResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GeometricNonTerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.LTLInfiniteCounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.LassoShapedNonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.core.lib.results.NonTerminationArgumentResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.NonterminatingLassoResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TerminationAnalysisResult.Termination;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType.Type;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.BacktranslationUtil;
import de.uni_freiburg.informatik.ultimate.lassoranker.NonterminationArgumentStatistics;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.GeometricNonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.InfiniteFixpointRepetition;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.InfiniteFixpointRepetitionWithExecution;
import de.uni_freiburg.informatik.ultimate.lassoranker.nontermination.NonTerminationArgument;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgPetrifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar.BuchiCegarLoopFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar.BuchiCegarLoopResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar.BuchiCegarLoopResult.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessModelToAutomatonTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.AutomataTestFileAST;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Jan Leike (leike@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
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
			if (mWitnessNode != null) {
				throw new UnsupportedOperationException("two witness models");
			}
			mWitnessNode = (WitnessNode) root;
		}
		if (root instanceof AutomataTestFileAST) {
			mAutomataTestFileAsts.add((AutomataTestFileAST) root);
		}
		return false;
	}

	private <L extends IIcfgTransition<?>> BuchiCegarLoopResult<L> runCegarLoops(final IIcfg<?> icfg,
			final INestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton,
			final BuchiCegarLoopFactory<L> factory) throws IOException {
		if (!IcfgUtils.isConcurrent(icfg)) {
			return factory.constructCegarLoop(icfg, witnessAutomaton).runCegarLoop();
		}
		int numberOfThreadInstances = 1;
		while (true) {
			final IcfgPetrifier icfgPetrifier = new IcfgPetrifier(mServices, icfg, numberOfThreadInstances, true);
			mServices.getBacktranslationService().addTranslator(icfgPetrifier.getBacktranslator());
			final IIcfg<IcfgLocation> petrified = icfgPetrifier.getPetrifiedIcfg();
			final BuchiCegarLoopResult<L> result =
					factory.constructCegarLoop(petrified, witnessAutomaton).runCegarLoop();
			if (result.getResult() != Result.INSUFFICIENT_THREADS) {
				return result;
			}
			mLogger.warn(numberOfThreadInstances
					+ " thread instances were not sufficient, I will increase this number and restart the analysis");
			numberOfThreadInstances++;
		}
	}

	private IIcfg<?> doTerminationAnalysis(final IIcfg<?> icfg,
			final INestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) throws IOException, AssertionError {
		final BuchiCegarLoopBenchmarkGenerator benchGen = new BuchiCegarLoopBenchmarkGenerator();
		final BuchiCegarLoopResult<IcfgEdge> result = runCegarLoops(icfg, witnessAutomaton,
				new BuchiCegarLoopFactory<>(mServices, new TAPreferences(mServices), IcfgEdge.class, benchGen));

		benchGen.stop(CegarLoopStatisticsDefinitions.OverallTime);

		final IResult benchDecomp = new StatisticsResult<>(Activator.PLUGIN_ID, "Constructed decomposition of program",
				result.getMDBenchmark());

		reportResult(benchDecomp);

		final boolean constructTermcompProof = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_CONSTRUCT_TERMCOMP_PROOF);
		if (constructTermcompProof) {
			final IResult termcompProof = new StatisticsResult<>(Activator.PLUGIN_ID,
					"Constructed termination proof in form of nested word automata",
					result.getTermcompProofBenchmark());
			reportResult(termcompProof);
		}

		final BuchiAutomizerTimingBenchmark timingBenchmark = new BuchiAutomizerTimingBenchmark(benchGen);
		final IResult benchTiming = new StatisticsResult<>(Activator.PLUGIN_ID, "Timing statistics", timingBenchmark);
		reportResult(benchTiming);

		interpretAndReportResult(result, icfg);
		return icfg;
	}

	/**
	 * Get a nontermination argument back to report.
	 */
	private NonTerminationArgumentResult<IcfgEdge, Term> getNonTerminationResult(final NonTerminationArgument nta,
			final IcfgProgramExecution<IcfgEdge> stemExecution, final IcfgProgramExecution<IcfgEdge> loopExecution,
			final IcfgEdge hondaAction) {
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

			return new GeometricNonTerminationArgumentResult<>(hondaAction, Activator.PLUGIN_NAME, initHondaRays.get(0),
					initHondaRays.get(1), initHondaRays.subList(2, initHondaRays.size()), gnta.getLambdas(),
					gnta.getNus(), mServices.getBacktranslationService(), Term.class, stemExecution, loopExecution);
		}
		if (nta instanceof InfiniteFixpointRepetitionWithExecution) {
			return new LassoShapedNonTerminationArgument<>(hondaAction, Activator.PLUGIN_NAME,
					mServices.getBacktranslationService(), Term.class, stemExecution, loopExecution);
		}
		if (nta instanceof InfiniteFixpointRepetition) {
			final InfiniteFixpointRepetition ifr = (InfiniteFixpointRepetition) nta;
			return new FixpointNonTerminationResult<>(hondaAction, Activator.PLUGIN_NAME, ifr.getValuesAtInit(),
					ifr.getValuesAtHonda(), mServices.getBacktranslationService(), Term.class, stemExecution,
					loopExecution);
		}
		throw new IllegalArgumentException("Unknown NonTerminationArgument " + nta.getClass());
	}

	private void interpretAndReportResult(final BuchiCegarLoopResult<IcfgEdge> result, final IIcfg<?> icfg)
			throws AssertionError {
		final LTLPropertyCheck ltlAnnot = LTLPropertyCheck.getAnnotation(icfg);
		final String whatToProve = ltlAnnot != null ? ltlAnnot.getUltimateLTLProperty() : "termination";
		switch (result.getResult()) {
		case NONTERMINATING:
			reportNonTermination(result, ltlAnnot);
			return;
		case TERMINATING:
			reportTermination(ltlAnnot);
			return;
		case TIMEOUT:
			reportTimeout(result, whatToProve);
			return;
		case UNKNOWN:
			reportUnknown(result, whatToProve);
			return;
		default:
			throw new AssertionError("Extend the switch with the new enum member " + result);
		}
	}

	private void reportTermination(final LTLPropertyCheck ltlAnnot) {
		if (ltlAnnot == null) {
			final String longDescr = "Buchi Automizer proved that your program is terminating";
			reportResult(new TerminationAnalysisResult(Activator.PLUGIN_ID, Termination.TERMINATING, longDescr));
		} else {
			// The LTL property holds
			reportResult(new AllSpecificationsHoldResult(Activator.PLUGIN_ID,
					"Buchi Automizer proved that the LTL property " + ltlAnnot.getUltimateLTLProperty() + " holds"));
		}
	}

	private void reportNonTermination(final BuchiCegarLoopResult<IcfgEdge> result, final LTLPropertyCheck ltlAnnot) {
		final IcfgProgramExecution<IcfgEdge> stemPE;
		if (result.getStem().length() == 0) {
			stemPE = IcfgProgramExecution.create(IcfgEdge.class);
		} else {
			if (result.getNonTerminationArgument() instanceof InfiniteFixpointRepetitionWithExecution) {
				stemPE = (IcfgProgramExecution<IcfgEdge>) ((InfiniteFixpointRepetitionWithExecution) result
						.getNonTerminationArgument()).getStemExecution();
			} else {
				stemPE = TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(result.getStem());
			}
		}
		final IcfgProgramExecution<IcfgEdge> loopPE = TraceCheckUtils
				.computeSomeIcfgProgramExecutionWithoutValues(result.getLoop());
		final IcfgEdge hondaAction = result.getLoop().getSymbol(0);

		if (ltlAnnot == null) {
			final String longDescr = "Buchi Automizer proved that your program is nonterminating for some inputs";
			reportResult(new TerminationAnalysisResult(Activator.PLUGIN_ID, Termination.NONTERMINATING, longDescr));

			final NonTerminationArgument nta = result.getNonTerminationArgument();
			reportResult(getNonTerminationResult(nta, stemPE, loopPE, hondaAction));
			reportResult(new StatisticsResult<>(Activator.PLUGIN_NAME,
					NonterminationArgumentStatistics.class.getSimpleName(), new NonterminationArgumentStatistics(nta)));
			reportResult(new NonterminatingLassoResult<>(hondaAction, Activator.PLUGIN_ID,
					mServices.getBacktranslationService(), stemPE, loopPE));
		} else {
			// There is a violation of the LTL property
			reportResult(new LTLInfiniteCounterExampleResult<>(hondaAction, Activator.PLUGIN_ID,
					mServices.getBacktranslationService(), stemPE, loopPE, ltlAnnot.getUltimateLTLProperty()));
		}
	}

	private void reportUnknown(final BuchiCegarLoopResult<IcfgEdge> result, final String whatToProve) {
		final Map<String, ILocation> overapprox = result.getOverapproximations();
		final StringBuilder longDescr = new StringBuilder();
		if (overapprox.isEmpty()) {
			longDescr.append("Buchi Automizer is unable to decide " + whatToProve + " for the following lasso. ");
		} else {
			longDescr.append("Buchi Automizer cannot decide " + whatToProve
					+ " for the following lasso because it contains the following overapproximations. ");
			longDescr.append(CoreUtil.getPlatformLineSeparator());
			longDescr.append("Overapproximations");
			longDescr.append(CoreUtil.getPlatformLineSeparator());
			for (final Entry<String, ILocation> oa : overapprox.entrySet()) {
				longDescr.append(String.format("%s (Reason %s)", oa.getValue(), oa.getKey()));
			}
			longDescr.append(CoreUtil.getPlatformLineSeparator());
			longDescr.append("Lasso");
		}
		longDescr.append(CoreUtil.getPlatformLineSeparator());
		longDescr.append("Stem: ");
		longDescr.append(result.getStem());
		longDescr.append(CoreUtil.getPlatformLineSeparator());
		longDescr.append("Loop: ");
		longDescr.append(result.getLoop());
		reportResult(new TerminationAnalysisResult(Activator.PLUGIN_ID, Termination.UNKNOWN, longDescr.toString()));
	}

	private void reportTimeout(final BuchiCegarLoopResult<IcfgEdge> result, final String whatToProve) {
		final String longDescr = "Buchi Automizer is unable to decide " + whatToProve + ": Timeout "
				+ result.getToolchainCancelledException().printRunningTaskMessage();
		reportResult(new TimeoutResult(Activator.PLUGIN_ID, longDescr));
	}

	private void reportResult(final IResult res) {
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
}
