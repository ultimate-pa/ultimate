/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonEpimorphism;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.ITransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsAggregator;

public class TotalInterpolationAutomatonBuilder<LETTER extends IIcfgTransition<?>>
		implements IInterpolantAutomatonBuilder<LETTER, IPredicate> {

	private final List<IPredicate> mStateSequence;
	private final NestedWordAutomaton<LETTER, IPredicate> mIA;
	private final PredicateFactory mPredicateFactory;
	private final IPredicateUnifier mPredicateUnifier;
	private final INestedWordAutomaton<LETTER, IPredicate> mAbstraction;

	private final CfgSmtToolkit mCsToolkit;

	private final ArrayDeque<IPredicate> mWorklist = new ArrayDeque<>();
	private final Set<IPredicate> mAnnotated = new HashSet<>();

	private final AutomatonEpimorphism<IPredicate> mEpimorphism;
	private final IHoareTripleChecker mHtc;
	private final InterpolationTechnique mInterpolation;

	private final TotalInterpolationBenchmarkGenerator mBenchmarkGenerator;
	private final IUltimateServiceProvider mServices;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final boolean mCollectInterpolantStatistics;

	public TotalInterpolationAutomatonBuilder(final INestedWordAutomaton<LETTER, IPredicate> abstraction,
			final NestedRun<LETTER, IPredicate> nestedRun, final CfgSmtToolkit csToolkit,
			final PredicateFactoryForInterpolantAutomata predicateFactory, final InterpolationTechnique interpolation,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final boolean collectInterpolantStatistics,
			final IPredicateUnifier predicateUnifier, final TracePredicates ipp)
			throws AutomataOperationCanceledException {
		mServices = services;
		mBenchmarkGenerator = new TotalInterpolationBenchmarkGenerator(mServices.getStorage());
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mCollectInterpolantStatistics = collectInterpolantStatistics;
		mStateSequence = nestedRun.getStateSequence();
		mCsToolkit = csToolkit;
		mPredicateUnifier = predicateUnifier;
		mPredicateFactory = (PredicateFactory) mPredicateUnifier.getPredicateFactory();
		mAbstraction = abstraction;
		final VpAlphabet<LETTER> alphabet = NestedWordAutomataUtils.getVpAlphabet(abstraction);
		mIA = new StraightLineInterpolantAutomatonBuilder<>(mServices, null, alphabet, Collections.singletonList(ipp),
				predicateFactory,
				StraightLineInterpolantAutomatonBuilder.InitialAndAcceptingStateMode.ONLY_FIRST_INITIAL_ONLY_FALSE_ACCEPTING)
						.getResult();
		mInterpolation = interpolation;
		mEpimorphism = new AutomatonEpimorphism<>(new AutomataLibraryServices(mServices));
		{
			final IPredicate firstAutomatonState = mStateSequence.get(0);
			mEpimorphism.insert(firstAutomatonState, ipp.getPrecondition());
			mAnnotated.add(firstAutomatonState);
			mWorklist.add(firstAutomatonState);
		}
		addInterpolants(mStateSequence, ipp.getPredicates());
		{
			final IPredicate lastAutomatonState = mStateSequence.get(mStateSequence.size() - 1);
			mEpimorphism.insert(lastAutomatonState, ipp.getPostcondition());
			mAnnotated.add(lastAutomatonState);
			mWorklist.add(lastAutomatonState);
		}
		mHtc = HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(services,
				HoareTripleChecks.INCREMENTAL, mCsToolkit, mPredicateUnifier);
		for (final IPredicate state : nestedRun.getStateSequence()) {
			mWorklist.add(state);
			mAnnotated.add(state);
		}
		while (!mWorklist.isEmpty()) {
			final IPredicate p = mWorklist.removeFirst();
			doThings(p);
		}
		mBenchmarkGenerator.addEdgeCheckerData(mHtc.getStatistics());
	}

	private void doThings(final IPredicate p) throws AutomataOperationCanceledException {
		for (final OutgoingInternalTransition<LETTER, IPredicate> transition : mAbstraction.internalSuccessors(p)) {
			continueCheckForOutgoingPath(p, transition, transition.getSucc());
		}
		for (final OutgoingCallTransition<LETTER, IPredicate> transition : mAbstraction.callSuccessors(p)) {
			continueCheckForOutgoingPath(p, transition, transition.getSucc());
		}
		for (final OutgoingReturnTransition<LETTER, IPredicate> transition : mAbstraction.returnSuccessors(p)) {
			if (mAnnotated.contains(transition.getHierPred())) {
				continueCheckForOutgoingPath(p, transition, transition.getSucc());
			}
		}

	}

	private void continueCheckForOutgoingPath(final IPredicate p, final ITransitionlet<LETTER, IPredicate> transition,
			final IPredicate succ) throws AutomataOperationCanceledException {
		if (mAnnotated.contains(succ)) {
			final IPredicate predItp = mEpimorphism.getMapping(p);
			final IPredicate succItp = mEpimorphism.getMapping(succ);
			// this is a one-step path, no need to call traceCheck
			if (interpolantAutomatonContainsTransition(predItp, transition, succItp)) {
				// do nothing, transition is already contained
			} else {
				mBenchmarkGenerator.incrementPathLenght1();
				checkRunOfLenthOne(predItp, transition, succItp);
			}
		} else {
			mBenchmarkGenerator.incrementRunSearches();
			final NestedRun<LETTER, IPredicate> runStartingInSucc = findRun(succ, mAnnotated);
			if (runStartingInSucc != null) {
				final NestedRun<LETTER, IPredicate> firstStep = constructRunOfLengthOne(p, transition);
				final NestedRun<LETTER, IPredicate> completeRun = firstStep.concatenate(runStartingInSucc);
				checkRun(completeRun);
			}
		}

	}

	/**
	 * Check if automaton contains transition (predItp, internalTrans.getLetter(), succItp) We take from the transition
	 * only the letter!
	 */
	private boolean interpolantAutomatonContainsTransition(final IPredicate predItp,
			final ITransitionlet<LETTER, IPredicate> transition, final IPredicate succItp) {
		if (transition instanceof OutgoingInternalTransition) {
			final OutgoingInternalTransition<LETTER, IPredicate> internalTrans =
					(OutgoingInternalTransition<LETTER, IPredicate>) transition;
			final Set<IPredicate> succs = mIA.succInternal(predItp, internalTrans.getLetter());
			return succs.contains(succItp);
		}
		if (transition instanceof OutgoingCallTransition) {
			final OutgoingCallTransition<LETTER, IPredicate> callTrans =
					(OutgoingCallTransition<LETTER, IPredicate>) transition;
			final Set<IPredicate> succs = mIA.succCall(predItp, callTrans.getLetter());
			return succs.contains(succItp);
		}
		if (transition instanceof OutgoingReturnTransition) {
			final OutgoingReturnTransition<LETTER, IPredicate> returnTrans =
					(OutgoingReturnTransition<LETTER, IPredicate>) transition;
			final IPredicate hierPredItp = mEpimorphism.getMapping(returnTrans.getHierPred());
			final Set<IPredicate> succs = mIA.succReturn(predItp, hierPredItp, returnTrans.getLetter());
			return succs.contains(succItp);
		}
		if (transition instanceof SummaryReturnTransition) {
			final SummaryReturnTransition<LETTER, IPredicate> summaryTrans =
					(SummaryReturnTransition<LETTER, IPredicate>) transition;
			final IPredicate linPredItp = mEpimorphism.getMapping(summaryTrans.getLinPred());
			final Set<IPredicate> succs = mIA.succReturn(linPredItp, predItp, summaryTrans.getLetter());
			return succs != null && succs.contains(succItp);
		}
		throw new AssertionError("unsupported" + transition.getClass());
	}

	private NestedRun<LETTER, IPredicate> constructRunOfLengthOne(final IPredicate p,
			final ITransitionlet<LETTER, IPredicate> transition) {
		if (transition instanceof OutgoingInternalTransition) {
			final OutgoingInternalTransition<LETTER, IPredicate> internalTrans =
					(OutgoingInternalTransition<LETTER, IPredicate>) transition;
			return new NestedRun<>(p, internalTrans.getLetter(), NestedWord.INTERNAL_POSITION, internalTrans.getSucc());
		}
		if (transition instanceof OutgoingCallTransition) {
			final OutgoingCallTransition<LETTER, IPredicate> callTrans =
					(OutgoingCallTransition<LETTER, IPredicate>) transition;
			return new NestedRun<>(p, callTrans.getLetter(), NestedWord.PLUS_INFINITY, callTrans.getSucc());
		}
		if (transition instanceof OutgoingReturnTransition) {
			final OutgoingReturnTransition<LETTER, IPredicate> returnTrans =
					(OutgoingReturnTransition<LETTER, IPredicate>) transition;
			return new NestedRun<>(p, returnTrans.getLetter(), NestedWord.MINUS_INFINITY, returnTrans.getSucc());
		}
		if (transition instanceof SummaryReturnTransition) {
			final SummaryReturnTransition<LETTER, IPredicate> summaryTrans =
					(SummaryReturnTransition<LETTER, IPredicate>) transition;
			return new NestedRun<>(summaryTrans.getLinPred(), summaryTrans.getLetter(), NestedWord.MINUS_INFINITY,
					summaryTrans.getSucc());
		}
		throw new AssertionError("unsupported" + transition.getClass());

	}

	private void checkRunOfLenthOne(final IPredicate predItp, final ITransitionlet<LETTER, IPredicate> transition,
			final IPredicate succItp) {
		if (transition instanceof OutgoingInternalTransition) {
			final OutgoingInternalTransition<LETTER, IPredicate> internalTrans =
					(OutgoingInternalTransition<LETTER, IPredicate>) transition;
			final Validity validity = mHtc.checkInternal(predItp, (IInternalAction) transition.getLetter(), succItp);
			if (validity == Validity.VALID) {
				mIA.addInternalTransition(predItp, internalTrans.getLetter(), succItp);
			}
		} else if (transition instanceof OutgoingCallTransition) {
			final OutgoingCallTransition<LETTER, IPredicate> callTrans =
					(OutgoingCallTransition<LETTER, IPredicate>) transition;
			final Validity validity = mHtc.checkCall(predItp, (ICallAction) callTrans.getLetter(), succItp);
			if (validity == Validity.VALID) {
				mIA.addCallTransition(predItp, callTrans.getLetter(), succItp);
			}
		} else if (transition instanceof OutgoingReturnTransition) {
			final OutgoingReturnTransition<LETTER, IPredicate> returnTrans =
					(OutgoingReturnTransition<LETTER, IPredicate>) transition;
			final IPredicate hierPredItp = mEpimorphism.getMapping(returnTrans.getHierPred());
			final Validity validity =
					mHtc.checkReturn(predItp, hierPredItp, (IReturnAction) returnTrans.getLetter(), succItp);
			if (validity == Validity.VALID) {
				mIA.addReturnTransition(predItp, hierPredItp, returnTrans.getLetter(), succItp);
			}
		} else if (transition instanceof SummaryReturnTransition) {
			final SummaryReturnTransition<LETTER, IPredicate> summaryTrans =
					(SummaryReturnTransition<LETTER, IPredicate>) transition;
			final IPredicate linPredItp = mEpimorphism.getMapping(summaryTrans.getLinPred());
			final Validity validity =
					mHtc.checkReturn(linPredItp, predItp, (IReturnAction) summaryTrans.getLetter(), succItp);
			if (validity == Validity.VALID) {
				mIA.addReturnTransition(linPredItp, predItp, summaryTrans.getLetter(), succItp);
			}
		} else {
			throw new AssertionError("unsupported" + transition.getClass());
		}
	}

	private void checkRun(final NestedRun<LETTER, IPredicate> run) {
		final IPredicate first = run.getStateAtPosition(0);
		final IPredicate last = run.getStateAtPosition(run.getLength() - 1);
		final IPredicate precondition = mEpimorphism.getMapping(first);
		final IPredicate postcondition = mEpimorphism.getMapping(last);
		final SortedMap<Integer, IPredicate> pendingContexts = computePendingContexts(run);

		InterpolatingTraceCheck<LETTER> tc;
		switch (mInterpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation:
			tc = new InterpolatingTraceCheckCraig<>(precondition, postcondition, pendingContexts, run.getWord(),
					run.getStateSequence(), mServices, mCsToolkit, mPredicateFactory, mPredicateUnifier,
					AssertCodeBlockOrder.NOT_INCREMENTALLY, false, mCollectInterpolantStatistics, mInterpolation, true,
					mXnfConversionTechnique, mSimplificationTechnique);
			break;
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
		case FPandBPonlyIfFpWasNotPerfect:
			tc = new TraceCheckSpWp<>(precondition, postcondition, pendingContexts, run.getWord(), mCsToolkit,
					AssertCodeBlockOrder.NOT_INCREMENTALLY, UnsatCores.CONJUNCT_LEVEL, true, mServices, false,
					mPredicateFactory, mPredicateUnifier, mInterpolation, mCsToolkit.getManagedScript(),
					mXnfConversionTechnique, mSimplificationTechnique, run.getStateSequence(),
					mCollectInterpolantStatistics);
			break;
		case PathInvariants:
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
		mBenchmarkGenerator.addTraceCheckData(tc.getStatistics());
		if (tc.isCorrect() == LBool.UNSAT) {
			mBenchmarkGenerator.incrementUsefullRunGeq2();
			final int additionalInterpolants = addInterpolants(run.getStateSequence(), tc.getInterpolants());
			mBenchmarkGenerator.reportAdditionalInterpolants(additionalInterpolants);
			addTransitions(run.getStateSequence(), tc);
		} else {
			mBenchmarkGenerator.incrementUselessRunGeq2();
		}
	}

	private SortedMap<Integer, IPredicate> computePendingContexts(final NestedRun<LETTER, IPredicate> run) {
		final SortedMap<Integer, IPredicate> result = new TreeMap<>();
		for (final int pendingReturnPos : run.getWord().getPendingReturns().keySet()) {
			final IPredicate linPred = run.getStateAtPosition(pendingReturnPos);
			final Iterable<IPredicate> hierPreds = NestedWordAutomataUtils.hierarchicalPredecessorsOutgoing(linPred,
					run.getSymbol(pendingReturnPos), mAbstraction);
			final IPredicate hierPred = getSomeAnnotatedState(hierPreds);
			if (hierPred == null) {
				throw new AssertionError("found nothing");
			}
			result.put(pendingReturnPos, mEpimorphism.getMapping(hierPred));
		}
		return result;
	}

	private IPredicate getSomeAnnotatedState(final Iterable<IPredicate> states) {
		for (final IPredicate state : states) {
			if (mAnnotated.contains(state)) {
				return state;
			}
		}
		return null;
	}

	private void addTransitions(final ArrayList<IPredicate> stateSequence, final InterpolatingTraceCheck<LETTER> tc) {
		final TracePredicates ipp = new TracePredicates(tc);
		final NestedWord<LETTER> nw = TraceCheckUtils.toNestedWord(tc.getTrace());
		for (int i = 0; i < nw.length(); i++) {
			if (nw.isInternalPosition(i)) {
				mIA.addInternalTransition(ipp.getPredicate(i), nw.getSymbol(i), ipp.getPredicate(i + 1));
			} else if (nw.isCallPosition(i)) {
				mIA.addCallTransition(ipp.getPredicate(i), nw.getSymbol(i), ipp.getPredicate(i + 1));
			} else if (nw.isReturnPosition(i)) {
				IPredicate hierPred;
				if (nw.isPendingReturn(i)) {
					hierPred = tc.getPendingContexts().get(i);
				} else {
					final int callPredPos = nw.getCallPosition(i);
					hierPred = ipp.getPredicate(callPredPos);
				}
				mIA.addReturnTransition(ipp.getPredicate(i), hierPred, nw.getSymbol(i), ipp.getPredicate(i + 1));
			} else {
				throw new AssertionError();
			}
		}
	}

	private int addInterpolants(final List<IPredicate> stateSequence, final IPredicate[] interpolants) {
		return addInterpolants(stateSequence, Arrays.asList(interpolants));
	}

	/**
	 * Add a sequence of interpolants itp_1,...,itp_{n-1} for a sequence of states s_0,...,s_n. For each i add itp_i to
	 * the interpolant automaton if not already contained add s_i to the worklist add s_i to the annotated states add
	 * (s_i, itp_i) to the epimorphism Return the number of (different) interpolants that have been in the automaton
	 * before.
	 */
	private int addInterpolants(final List<IPredicate> stateSequence, final List<IPredicate> interpolants) {
		int numberOfNewPredicates = 0;
		int i = 0;
		for (final IPredicate interpolant : interpolants) {
			final IPredicate state = stateSequence.get(i + 1);
			if (!mIA.getStates().contains(interpolant)) {
				mIA.addState(false, false, interpolant);
				numberOfNewPredicates++;
			}
			mAnnotated.add(state);
			mEpimorphism.insert(state, interpolant);
			mWorklist.add(state);
			i++;
		}
		return numberOfNewPredicates;
	}

	private NestedRun<LETTER, IPredicate> findRun(final IPredicate p, final Set<IPredicate> annotated)
			throws AutomataOperationCanceledException {
		return new IsEmpty<>(new AutomataLibraryServices(mServices), mAbstraction, Collections.singleton(p),
				Collections.emptySet(), mAnnotated).getNestedRun();
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResult() {
		return mIA;
	}

	public TotalInterpolationBenchmarkGenerator getTotalInterpolationBenchmark() {
		return mBenchmarkGenerator;
	}

	public static class TotalInterpolationBenchmarkGenerator extends BaseStatisticsDataProvider {

		@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
		private int mAdditionalInterpolants;

		@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
		private int mPathLenght1;

		@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
		private int mRunSearches;

		@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
		private int mUsefullRunGeq2;

		@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
		private int mUselessRunGeq2;

		@Statistics(type = DefaultMeasureDefinitions.STATISTICS_AGGREGATOR)
		private final StatisticsAggregator mEcData;

		@Statistics(type = DefaultMeasureDefinitions.STATISTICS_AGGREGATOR)
		private final StatisticsAggregator mTcData;

		public TotalInterpolationBenchmarkGenerator(final IToolchainStorage storage) {
			super(storage);
			mEcData = new StatisticsAggregator(storage);
			mTcData = new StatisticsAggregator(storage);
		}

		public void reportAdditionalInterpolants(final int additionalInterpolants) {
			mAdditionalInterpolants += additionalInterpolants;
		}

		public void incrementPathLenght1() {
			mPathLenght1++;
		}

		public void incrementRunSearches() {
			mRunSearches++;
		}

		public void incrementUsefullRunGeq2() {
			mUsefullRunGeq2++;
		}

		public void incrementUselessRunGeq2() {
			mUselessRunGeq2++;
		}

		public void addEdgeCheckerData(final IStatisticsDataProvider ecbd) {
			mEcData.aggregateStatisticsData(ecbd);
		}

		public void addTraceCheckData(final IStatisticsDataProvider tcbd) {
			mTcData.aggregateStatisticsData(tcbd);
		}

	}

}
