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
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ITraceChecker;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;

/**
 * A provider class for the PartialOrderCegarLoop which can be called to extend the current interpolant automaton 
 * with additional states and transitions allowing conditional commutativity.
 *
 * @author Marcel Ebbinghaus
 *
 *@param <L>
 *            The type of letters.
 */
public class ConditionalCommutativityInterpolantProvider<L extends IAction> {

	private final ConditionalCommutativityChecker<L> mChecker;
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mReduction;
	private final IUltimateServiceProvider mServices;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackStateFactory;
	private NestedWordAutomaton<L, IPredicate> mCopy;
	private IRun<L, IPredicate> mRun;

	/**
	 * Constructs a new instance of ConditionalCommutativityInterpolantProvider.
	 *
	 * @param services
	 *            Ultimate services
	 * @param criterion
	 *            An IConditionalCommutativityCriterion to decide when to check for conditional commutativity
	 * @param independenceRelation
	 * 			  The independence relation used for the reduction
	 * @param generator
	 * 			  Generator for constructing commutativity conditions
	 * @param abstraction
	 * 			  Current abstraction
	 * @param reduction
	 * 			  Reduction of abstraction
	 * @param emptyStackStateFactory
	 * 			  Factory
	 * @param traceChecker
	 * 			  An ITraceChecker responsible for checking whether a condition is feasible 
	 */
	public ConditionalCommutativityInterpolantProvider(final IUltimateServiceProvider services,
			final IConditionalCommutativityCriterion<L, IPredicate> criterion,
			final IIndependenceRelation<IPredicate, L> independenceRelation,
			final IIndependenceConditionGenerator generator, final IAutomaton<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> reduction,
			final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory, final ITraceChecker<L> traceChecker) {
		mServices = services;
		mReduction = reduction;
		mEmptyStackStateFactory = emptyStackStateFactory;
		mChecker = new ConditionalCommutativityChecker<>(criterion, generator, traceChecker);
	}

	/**
	 * Constructs a copy of interpolantAutomaton and adds states and transitions for conditional commutativity
	 * along a given run.
	 *
	 * @param run
	 *            The run
	 * @param interpolantAutomaton
	 *            The interpolant automaton
	 * @return mCopy
	 * 			  The extended copy of interpolantAutomaton 
	 */
	public NestedWordAutomaton<L, IPredicate> getInterpolants(final IRun<L, IPredicate> run,
			final NestedWordAutomaton<L, IPredicate> interpolantAutomaton) {
		mRun = run;
		mCopy = createCopy(interpolantAutomaton);
		int a=0;
		for (IPredicate state : mRun.getStateSequence()) {
			//state = ((SleepPredicate) state);
			final Iterator<OutgoingInternalTransition<L, IPredicate>> iterator =
					mReduction.internalSuccessors(((SleepPredicate) state).getUnderlying()).iterator();
			final List<OutgoingInternalTransition<L, IPredicate>> transitions = new ArrayList<>();
			while (iterator.hasNext()) {
				transitions.add(iterator.next());
			}
			int b=0;
			for (int j = 0; j < transitions.size(); j++) {
				final OutgoingInternalTransition<L, IPredicate> transition1 = transitions.get(j);
				for (int k = j + 1; k < transitions.size(); k++) {
					final OutgoingInternalTransition<L, IPredicate> transition2 = transitions.get(k);
					final TracePredicates tracePredicates = mChecker.checkConditionalCommutativity(mRun, state,
							transition1.getLetter(), transition2.getLetter());

					List<IPredicate> conPredicates = new ArrayList<>();
					if (tracePredicates != null) {
						conPredicates.addAll(tracePredicates.getPredicates());
						conPredicates.add(tracePredicates.getPostcondition());
						addToCopy(conPredicates);
					}
				}
			}
		}
		return mCopy;
	}

	private void addToCopy(final List<IPredicate> conPredicates) {
			// add states and transitions to copy
		mCopy.addState(true, false, conPredicates.get(0));
		for (Integer i = 1; i < conPredicates.size(); i++) {
			final IPredicate succPred = conPredicates.get(i);
			mCopy.addState(false, i.equals(conPredicates.size() - 1), succPred);
			mCopy.addInternalTransition(conPredicates.get(i - 1), mRun.getWord().getSymbol(i - 1), succPred);
		}
	}

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
		for (IPredicate initState : interpolantAutomaton.getInitialStates()) {
			copy.addState(true, interpolantAutomaton.isFinal(initState), initState);
		}
		while (!deque.isEmpty()) {
			final IPredicate state = deque.pop();
			//if (!copy.contains(state)) {
				//copy.addState(interpolantAutomaton.isInitial(state), interpolantAutomaton.isFinal(state), state);
				for (final OutgoingInternalTransition<L, IPredicate> transition : interpolantAutomaton
						.internalSuccessors(state)) {
					IPredicate sucState = transition.getSucc();
					if (!copy.contains(sucState)) {
						copy.addState(false, interpolantAutomaton.isFinal(sucState), sucState);
						deque.push(sucState);
					}
					copy.addInternalTransition(state, transition.getLetter(), sucState);
					//deque.push(transition.getSucc());
				}
			//}	
		}
		return copy;
	}

}
