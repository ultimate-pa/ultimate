/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Given one sequence of n+1 pairwise disjoint interpolants and a word of length
 * n, this builder would construct the interpolant automaton that has the shape
 * of a straight line (hence the name). If several interpolants occur twice in
 * the sequence, we construct only one single state for them (resulting in a
 * straight line with selfloops). Furthermore, this builder supports as an input
 * several sequences that have the same precondition and the same postcondition.
 * Several sequences result in several straight lines where some states (those
 * that correspond to similar interpolants) were merged.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class StraightLineInterpolantAutomatonBuilder<LETTER> implements IInterpolantAutomatonBuilder<LETTER, IPredicate> {

	/**
	 * Determines which states become initial and accepting in the automaton.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum InitialAndAcceptingStateMode {
		/**
		 * Only the first state becomes initial and only the state whose predicate's
		 * term is syntactically equivalent to false becomes accepting.
		 */
		ONLY_FIRST_INITIAL_ONLY_FALSE_ACCEPTING,
		/**
		 * All states become initial and accepting.
		 */
		ALL_INITIAL_ALL_ACCEPTING
	}

	private final NestedWordAutomaton<LETTER, IPredicate> mResult;

	public StraightLineInterpolantAutomatonBuilder(final IUltimateServiceProvider services, final Word<LETTER> word,
			final VpAlphabet<LETTER> alphabet, final List<TracePredicates> interpolantSequences,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory,
			final InitialAndAcceptingStateMode initialAndAcceptingStateMode) {
		if (interpolantSequences.isEmpty()) {
			throw new IllegalArgumentException("Empty list of interpolant sequences is not allowed.");
		}
		assert sequencesHaveSamePrePostconditions(
				interpolantSequences) : "The interpolant sequences should have the same pre- and postconditions.";

		mResult = constructInterpolantAutomaton(services, alphabet, interpolantSequences, NestedWord.nestedWord(word),
				emptyStackFactory, initialAndAcceptingStateMode);
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResult() {
		return mResult;
	}

	private NestedWordAutomaton<LETTER, IPredicate> constructInterpolantAutomaton(
			final IUltimateServiceProvider services, final VpAlphabet<LETTER> alphabet,
			final List<TracePredicates> interpolantSequences, final NestedWord<LETTER> nestedWord,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory, final InitialAndAcceptingStateMode initialAndAcceptingStateMode) {

		final NestedWordAutomaton<LETTER, IPredicate> nwa =
				new NestedWordAutomaton<>(new AutomataLibraryServices(services), alphabet, emptyStackFactory);

		addStatesAccordingToPredicates(nwa, interpolantSequences, nestedWord, initialAndAcceptingStateMode);
		addBasicTransitions(nwa, interpolantSequences, nestedWord);

		return nwa;
	}

	/**
	 * Add a state for each forward predicate and for each backward predicate.
	 *
	 * @param nwa
	 *            the automaton to which the states are added
	 * @param interpolantSequences
	 *            sequences of interpolants
	 * @param nestedWord
	 *            trace along which the interpolants are constructed
	 */
	private void addStatesAccordingToPredicates(final NestedWordAutomaton<LETTER, IPredicate> nwa,
			final List<TracePredicates> interpolantSequences,
			final NestedWord<LETTER> nestedWord, final InitialAndAcceptingStateMode initialAndAcceptingStateMode) {
		// add initial state with precondition predicate
		{
			final IPredicate firstPredicate = interpolantSequences.get(0).getPrecondition();
			final boolean isInitial = true;
			final boolean isAccepting = isStateAccepting(initialAndAcceptingStateMode, firstPredicate);
			nwa.addState(isInitial, isAccepting, firstPredicate);
		}

		for (final TracePredicates interpolantSequence : interpolantSequences) {
			for (int i = 1; i < nestedWord.length() + 1; i++) {
				final IPredicate interpolant = interpolantSequence.getPredicate(i);
				if (!nwa.getStates().contains(interpolant)) {
					final boolean isInitial = (initialAndAcceptingStateMode == InitialAndAcceptingStateMode.ALL_INITIAL_ALL_ACCEPTING);
					final boolean isAccepting = isStateAccepting(initialAndAcceptingStateMode, interpolant);

					nwa.addState(false, isFalsePredicate(interpolant), interpolant);
				}
			}
		}
	}

	private boolean isStateAccepting(final InitialAndAcceptingStateMode initialAndAcceptingStateMode, final IPredicate predicate)
			throws AssertionError {
		boolean isAccepting;
		switch (initialAndAcceptingStateMode) {
		case ALL_INITIAL_ALL_ACCEPTING:
			isAccepting = true;
			break;
		case ONLY_FIRST_INITIAL_ONLY_FALSE_ACCEPTING:
			isAccepting = isFalsePredicate(predicate);
			break;
		default:
			throw new AssertionError("unknown value " + initialAndAcceptingStateMode);

		}
		return isAccepting;
	}

	/**
	 * @return {@code true} iff the formula of this predicate is syntactically equivalent to {@code false}
	 */
	private static boolean isFalsePredicate(final IPredicate predicate) {
		return SmtUtils.isFalse(predicate.getFormula());
	}

	/**
	 * Add basic transitions in 3 steps. 1. For each predicate type add a transition from the precondition to the first
	 * predicate. (i.e. add transition (preCondition, st_0, FP_0), add transition (preCondition, st_0, BP_0)) 2. For
	 * each predicate type add a transition from the previous predicate to the current predicate. (i.e. add transition
	 * (FP_i-1, st_i, FP_i), add transition (BP_i-1, st_i, BP_i)) 3. For each predicate type add a transition from the
	 * last predicate to the post-condition. (i.e. add transition (FP_n-1, st_n, postCondition), add transition (BP_n-1,
	 * st_n, postCondition))
	 *
	 * @param nwa
	 *            - the automaton to which the basic transition are added
	 * @param interpolantSequences
	 *            sequences of interpolants
	 * @param nestedWord
	 *            trace along which the interpolants are constructed
	 */
	private void addBasicTransitions(final NestedWordAutomaton<LETTER, IPredicate> nwa,
			final List<TracePredicates> interpolantSequences,
			final NestedWord<LETTER> nestedWord) {
		for (final TracePredicates interpolantSequence : interpolantSequences) {
			for (int i = 0; i < nestedWord.length(); i++) {
				addTransition(nwa, interpolantSequence, nestedWord, i);
			}
		}
	}

	private void addTransition(final NestedWordAutomaton<LETTER, IPredicate> nwa,
			final TracePredicates interpolantSequence, final NestedWord<LETTER> nestedWord,
			final int symbolPos) {
		final LETTER symbol = nestedWord.getSymbol(symbolPos);
		final IPredicate succ = interpolantSequence.getPredicate(symbolPos + 1);
		if (nestedWord.isCallPosition(symbolPos)) {
			final IPredicate pred = interpolantSequence.getPredicate(symbolPos);
			if (!nwa.containsCallTransition(pred, symbol, succ)) {
				nwa.addCallTransition(pred, symbol, succ);
			}
		} else if (nestedWord.isReturnPosition(symbolPos)) {
			final IPredicate pred = interpolantSequence.getPredicate(symbolPos);
			final int callPos = nestedWord.getCallPosition(symbolPos);
			final IPredicate hier = interpolantSequence.getPredicate(callPos);
			if (!nwa.containsReturnTransition(pred, hier, symbol, succ)) {
				nwa.addReturnTransition(pred, hier, symbol, succ);
			}
		} else {
			final IPredicate pred = interpolantSequence.getPredicate(symbolPos);
			if (!nwa.containsInternalTransition(pred, symbol, succ)) {
				nwa.addInternalTransition(pred, symbol, succ);
			}
		}
	}

	private static boolean sequencesHaveSamePrePostconditions(final List<TracePredicates> interpolantSequences) {
		final Iterator<TracePredicates> it = interpolantSequences.iterator();
		final TracePredicates first = it.next();

		final IPredicate precondition = first.getPrecondition();
		final IPredicate postcondition = first.getPostcondition();

		while (it.hasNext()) {
			final TracePredicates sequence = it.next();
			if (precondition != sequence.getPrecondition() || postcondition != sequence.getPostcondition()) {
				return false;
			}
		}
		return true;
	}
}
