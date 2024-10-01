/*
 * Copyright (C) 2023 Marcel Ebbinghaus
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ITraceChecker;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderReductionFacade.StateSplitter;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IConditionalCommutativityCheckerStatisticsUtils.ConditionalCommutativityStopwatches;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * A provider class for the PartialOrderCegarLoop which can be called to extend the current interpolant automaton with
 * additional states and transitions allowing conditional commutativity.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
public class ConditionalCommutativityInterpolantChecker<L extends IAction> {

	private final ConditionalCommutativityChecker<L> mChecker;
	private final IUltimateServiceProvider mServices;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackStateFactory;
	// private NestedWordAutomaton<L, IPredicate> mCopy;
	private IRun<L, IPredicate> mRun;
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mAbstraction;
	private final IConditionalCommutativityCheckerStatisticsUtils mStatisticsUtils;
	private ConditionalCommutativityInterpolantAutomatonProvider<L> mInterpolantAutomatonProvider;
	private StateSplitter<IPredicate> mStateSplitter;

	/**
	 * Constructs a new instance of ConditionalCommutativityInterpolantProvider.
	 *
	 * @param services
	 *            Ultimate services
	 * @param criterion
	 *            An IConditionalCommutativityCriterion to decide when to check for conditional commutativity
	 * @param independenceRelation
	 *            The independence relation used for the reduction
	 * @param script
	 *            Script for conjunction handling
	 * @param generator
	 *            Generator for constructing commutativity conditions
	 * @param abstraction
	 *            Current abstraction
	 * @param emptyStackStateFactory
	 *            Factory
	 * @param traceChecker
	 *            An ITraceChecker responsible for checking whether a condition is feasible
	 * @param statisticsUtils
	 *            Statistics
	 * @param predicateUnifier
	 */
	public ConditionalCommutativityInterpolantChecker(final IUltimateServiceProvider services,
			final IConditionalCommutativityCriterion<L> criterion,
			final IIndependenceRelation<IPredicate, L> independenceRelation, final ManagedScript script,
			final IIndependenceConditionGenerator generator,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction,
			final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory, final ITraceChecker<L> traceChecker,
			final IPredicateUnifier predicateUnifier,
			final IConditionalCommutativityCheckerStatisticsUtils statisticsUtils, StateSplitter<IPredicate> splitter) {
		mServices = services;
		mAbstraction = abstraction;
		mEmptyStackStateFactory = emptyStackStateFactory;
		mChecker = new ConditionalCommutativityChecker<>(criterion, independenceRelation, script, generator,
				traceChecker, statisticsUtils);
		mStatisticsUtils = statisticsUtils;
		mStateSplitter = splitter;
		mInterpolantAutomatonProvider = new ConditionalCommutativityInterpolantAutomatonProvider<>(services,
				abstraction, emptyStackStateFactory, predicateUnifier);
	}

	/**
	 * Constructs a copy of interpolantAutomaton and adds states and transitions for conditional commutativity along a
	 * given run.
	 *
	 * @param run
	 *            The run
	 * @param runPredicates
	 *            Predicates used as context for the generator
	 * @param interpolantAutomaton
	 *            The interpolant automaton
	 * @return mCopy The extended copy of interpolantAutomaton
	 */
	public NestedWordAutomaton<L, IPredicate> getInterpolants(final IRun<L, IPredicate> run,
			final List<IPredicate> runPredicates, final NestedWordAutomaton<L, IPredicate> interpolantAutomaton) {
		mStatisticsUtils.startStopwatch(ConditionalCommutativityStopwatches.OVERALL);
		mRun = run;
		mInterpolantAutomatonProvider.setInterPolantAutomaton(createCopy(interpolantAutomaton));
		// mCopy = createCopy(interpolantAutomaton);
		for (int i = 0; i < mRun.getStateSequence().size(); i++) {
			final IPredicate state = mRun.getStateSequence().get(i);
			IPredicate pred = mStateSplitter.getOriginal(state);

			final var transitions = DataStructureUtils.asList(mAbstraction.internalSuccessors(pred).iterator());
			if (checkState(state, transitions, i, runPredicates)) {
				// return mCopy;
				NestedWordAutomaton<L, IPredicate> automaton = mInterpolantAutomatonProvider.getInterpolantAutomaton();
				mStatisticsUtils.stopStopwatch(ConditionalCommutativityStopwatches.OVERALL);
				return automaton;
			}
		}
		// return mCopy;
		NestedWordAutomaton<L, IPredicate> automaton = mInterpolantAutomatonProvider.getInterpolantAutomaton();
		mStatisticsUtils.stopStopwatch(ConditionalCommutativityStopwatches.OVERALL);
		return automaton;
	}

	private boolean checkState(final IPredicate state,
			final List<OutgoingInternalTransition<L, IPredicate>> transitions, final int index,
			final List<IPredicate> runPredicates) {
		// TODO check if this works correctly for semi-commutativity
		for (int j = 0; j < transitions.size(); j++) {
			final OutgoingInternalTransition<L, IPredicate> transition1 = transitions.get(j);
			for (int k = j + 1; k < transitions.size(); k++) {
				final OutgoingInternalTransition<L, IPredicate> transition2 = transitions.get(k);
				final List<IPredicate> interpolantPredicates = new ArrayList<>();
				interpolantPredicates.addAll(
						getInterpolantPredicates(index, runPredicates.get(mRun.getStateSequence().indexOf(state))));
				NestedRun<L, IPredicate> currentRun = (NestedRun<L, IPredicate>) mRun;
				if (index != mRun.getStateSequence().size() - 1) {
					currentRun = currentRun.getSubRun(0, index);
				}
				if (checkTransitions(currentRun, interpolantPredicates, state, transition1.getLetter(),
						transition2.getLetter())) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean checkTransitions(final NestedRun<L, IPredicate> currentRun,
			final List<IPredicate> interpolantPredicates, final IPredicate state, final L letter1, final L letter2) {
		final TracePredicates tracePredicates =
				mChecker.checkConditionalCommutativity(currentRun, interpolantPredicates, state, letter1, letter2);

		final List<IPredicate> conPredicates = new ArrayList<>();
		if (tracePredicates != null) {
			conPredicates.add(tracePredicates.getPrecondition());
			conPredicates.addAll(tracePredicates.getPredicates());
			conPredicates.add(tracePredicates.getPostcondition());
			// addToCopy(conPredicates);
			mInterpolantAutomatonProvider.addToInterpolantAutomaton(conPredicates, currentRun.getWord());
			mStatisticsUtils.addIAIntegration();
		}
		return (!conPredicates.isEmpty()
				&& SmtUtils.isFalseLiteral(conPredicates.get(conPredicates.size() - 2).getFormula()));
	}

	private List<IPredicate> getInterpolantPredicates(final int runIndex, final IPredicate runPredicate) {
		List<IPredicate> interpolantPredicates = new ArrayList<>();
		if (runPredicate != null && !SmtUtils.isTrueLiteral(runPredicate.getFormula())) {
			interpolantPredicates.add(runPredicate);
		}
		if (runIndex == 0) {
			return interpolantPredicates;
		}

		// traverse mCopy and add
		List<IPredicate> worklist = new ArrayList<>();
		/*
		 * for (final IPredicate initState : mCopy.getInitialStates()) { worklist.add(initState); }
		 */
		for (final IPredicate initState : mInterpolantAutomatonProvider.getInterpolantAutomaton().getInitialStates()) {
			worklist.add(initState);
		}
		for (int i = 0; i < runIndex; i++) {
			final List<IPredicate> nextWorklist = new ArrayList<>();
			for (final IPredicate state : worklist) {
				/*
				 * final Iterator<OutgoingInternalTransition<L, IPredicate>> iterator = mCopy.internalSuccessors(state,
				 * mRun.getWord().getSymbol(i)).iterator();
				 */
				final Iterator<OutgoingInternalTransition<L, IPredicate>> iterator = mInterpolantAutomatonProvider
						.getInterpolantAutomaton().internalSuccessors(state, mRun.getWord().getSymbol(i)).iterator();

				while (iterator.hasNext()) {
					final IPredicate succ = iterator.next().getSucc();
					if (SmtUtils.isFalseLiteral(succ.getFormula())) {
						// interpolantPredicates.add(succ);
						interpolantPredicates = new ArrayList<>();
						interpolantPredicates.add(succ);
						return interpolantPredicates;
					}
					nextWorklist.add(succ);
				}
			}
			if (i == runIndex - 1) {
				for (final IPredicate pred : nextWorklist) {
					if (!SmtUtils.isTrueLiteral(pred.getFormula())) {
						interpolantPredicates.add(pred);
					}
				}
				// interpolantPredicates.addAll(nextWorklist);
			}
			worklist = nextWorklist;
		}
		return interpolantPredicates;
	}

	/*
	 * private void addToCopy(final List<IPredicate> conPredicates) { // add states and transitions to copy if
	 * (!mCopy.contains(conPredicates.get(0))) { mCopy.addState(true, false, conPredicates.get(0)); } for (Integer i =
	 * 1; i < conPredicates.size(); i++) { final IPredicate succPred = conPredicates.get(i); if
	 * (!mCopy.contains(succPred)) { mCopy.addState(false, false, succPred); }
	 * mCopy.addInternalTransition(conPredicates.get(i - 1), mRun.getWord().getSymbol(i - 1), succPred); } }
	 */

	private NestedWordAutomaton<L, IPredicate>
			createCopy(final NestedWordAutomaton<L, IPredicate> interpolantAutomaton) {

		final Set<L> alphabet = new HashSet<>();
		alphabet.addAll(interpolantAutomaton.getAlphabet());
		final VpAlphabet<L> vpAlphabet = new VpAlphabet<>(alphabet);
		final NestedWordAutomaton<L, IPredicate> copy =
				new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), vpAlphabet, mEmptyStackStateFactory);
		// DFS trough interpolantAutomaton to copy states and transitions
		final Deque<IPredicate> deque = new ArrayDeque<>();
		deque.addAll(interpolantAutomaton.getInitialStates());
		for (final IPredicate initState : interpolantAutomaton.getInitialStates()) {
			copy.addState(true, interpolantAutomaton.isFinal(initState), initState);
		}
		while (!deque.isEmpty()) {
			final IPredicate state = deque.pop();
			for (final OutgoingInternalTransition<L, IPredicate> transition : interpolantAutomaton
					.internalSuccessors(state)) {
				final IPredicate sucState = transition.getSucc();
				if (!copy.contains(sucState)) {
					copy.addState(false, interpolantAutomaton.isFinal(sucState), sucState);
					deque.push(sucState);
				}
				copy.addInternalTransition(state, transition.getLetter(), sucState);
			}
		}
		return copy;
	}
}
