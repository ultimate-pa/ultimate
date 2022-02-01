/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Check if an automaton is
 * <a href="https://en.wikipedia.org/wiki/Semi-deterministic_B%C3%BCchi_automaton">Semi-deterministic</a>.
 * 
 * @author Matthias Heizmann
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class IsSemiDeterministic<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final Set<STATE> mNondeterministicSuccessorOfAccepting = new HashSet<>();

	private final boolean mResult;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mOperand;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public IsSemiDeterministic(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		super(services);
		if (operand instanceof NestedWordAutomatonReachableStates) {
			mOperand = (NestedWordAutomatonReachableStates<LETTER, STATE>) operand;
		} else {
			mOperand = new NestedWordAutomatonReachableStates<>(mServices, operand);
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		iterate();
		mResult = mNondeterministicSuccessorOfAccepting.isEmpty();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " Operand is " + (mResult ? "" : "not") + "semideterministic."
				+ " There are " + mNondeterministicSuccessorOfAccepting
				+ "nondeterministic non-strict successors of accepting states.";
	}

	/**
	 * TODO Christian 2016-09-04: This method is not used outside this class. Should it be private?
	 */
	public void iterate() {
		final Set<DoubleDecker<STATE>> visited = new HashSet<>();
		final ArrayDeque<DoubleDecker<STATE>> worklist = new ArrayDeque<>();

		// step one: start with finals,
		//           add all non-call successors
		final Set<DoubleDecker<STATE>> finalDoubleDeckers = getFinalDoubleDeckers();
		visited.addAll(finalDoubleDeckers);
		worklist.addAll(finalDoubleDeckers);
		while (!worklist.isEmpty()) {
			final DoubleDecker<STATE> dd = worklist.remove();
			if (NestedWordAutomataUtils.isNondeterministic(dd.getUp(), dd.getDown(), mOperand)) {
				mNondeterministicSuccessorOfAccepting.add(dd.getUp());
			}
			final Set<DoubleDecker<STATE>> succs = getNonCallSuccessors(dd, mOperand);
			for (final DoubleDecker<STATE> succ : succs) {
				if (!visited.contains(succ)) {
					worklist.add(succ);
					visited.add(succ);
				}
			}
		}

		// step two: start with yet visited DoubleDeckers,
		//           add all non-return successors
		worklist.addAll(visited);
		while (!worklist.isEmpty()) {
			final DoubleDecker<STATE> dd = worklist.remove();
			if (NestedWordAutomataUtils.isNondeterministic(dd.getUp(), dd.getDown(), mOperand)) {
				mNondeterministicSuccessorOfAccepting.add(dd.getUp());
			}
			final Set<DoubleDecker<STATE>> succs = getNonReturnSuccessors(dd, mOperand);
			for (final DoubleDecker<STATE> succ : succs) {
				if (!visited.contains(succ)) {
					worklist.add(succ);
					visited.add(succ);
				}
			}
		}

	}

	private Set<DoubleDecker<STATE>> getFinalDoubleDeckers() {
		final Set<DoubleDecker<STATE>> result = new HashSet<>();
		for (final STATE fin : mOperand.getFinalStates()) {
			for (final STATE down : mOperand.getDownStates(fin)) {
				result.add(new DoubleDecker<>(down, fin));
			}
		}
		return result;
	}

	private static <LETTER, STATE> Set<DoubleDecker<STATE>> getNonCallSuccessors(final DoubleDecker<STATE> doubleDecker,
			final NestedWordAutomatonReachableStates<LETTER, STATE> nwa) {
		final Set<DoubleDecker<STATE>> succs = new HashSet<>();
		for (final OutgoingInternalTransition<LETTER, STATE> out : nwa.internalSuccessors(doubleDecker.getUp())) {
			succs.add(new DoubleDecker<>(doubleDecker.getDown(), out.getSucc()));
		}
		for (final SummaryReturnTransition<LETTER, STATE> out : nwa.summarySuccessors(doubleDecker.getUp())) {
			succs.add(new DoubleDecker<>(doubleDecker.getDown(), out.getSucc()));
		}
		for (final OutgoingReturnTransition<LETTER, STATE> out : nwa.returnSuccessorsGivenHier(doubleDecker.getUp(),
				doubleDecker.getDown())) {
			for (final STATE downOfHier : nwa.getDownStates(doubleDecker.getDown())) {
				succs.add(new DoubleDecker<>(downOfHier, out.getSucc()));
			}
		}
		return succs;
	}

	private static <LETTER, STATE> Set<DoubleDecker<STATE>> getNonReturnSuccessors(
			final DoubleDecker<STATE> doubleDecker, final NestedWordAutomatonReachableStates<LETTER, STATE> nwa) {
		final Set<DoubleDecker<STATE>> succs = new HashSet<>();
		for (final OutgoingInternalTransition<LETTER, STATE> out : nwa.internalSuccessors(doubleDecker.getUp())) {
			succs.add(new DoubleDecker<>(doubleDecker.getDown(), out.getSucc()));
		}
		for (final SummaryReturnTransition<LETTER, STATE> out : nwa.summarySuccessors(doubleDecker.getUp())) {
			succs.add(new DoubleDecker<>(doubleDecker.getDown(), out.getSucc()));
		}
		for (final OutgoingCallTransition<LETTER, STATE> out : nwa.callSuccessors(doubleDecker.getUp())) {
			succs.add(new DoubleDecker<>(doubleDecker.getUp(), out.getSucc()));
		}
		return succs;
	}



	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}
}
