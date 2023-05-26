/*
 * Copyright (C) 2022-2023 Daniel Küchler (kuechlerdaniel33@gmail.com)
 * Copyright (C) 2022-2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class that provides the Buchi acceptance check for (Buchi-)Petri nets.
 *
 * @param <LETTER>
 *            Symbol. Type of the symbols used as alphabet.
 * @param <STATE>
 *            Content. Type of the labels ("the content") of the automata states.
 * 
 * @author Daniel Küchler (kuechlerdaniel33@gmail.com)
 */
public final class BuchiAccepts<LETTER, PLACE> extends AcceptsInfiniteWords<LETTER, PLACE> {

	/**
	 * Constructor. Check if given Buchi-Petri Net accepts given word.
	 *
	 * @param <services>
	 *            Ultimare services.
	 *
	 * @param <operand>
	 *            Input Petri Net.
	 *
	 * @param <word>
	 *            Input word.
	 */
	public BuchiAccepts(final AutomataLibraryServices services,
			final IPetriNetTransitionProvider<LETTER, PLACE> operand, final NestedLassoWord<LETTER> word)
			throws PetriNetNot1SafeException {
		super(services, operand, word);
	}

	/**
	 * Creates a {@link MarkingOfFireSequence} with information if an accepted place was fired into.
	 */
	@Override
	MarkingOfFireSequence<LETTER, PLACE> getSuccessorMarkingOfFireSequence(
			final MarkingOfFireSequence<LETTER, PLACE> predecessor, final Transition<LETTER, PLACE> transition)
			throws PetriNetNot1SafeException {
		int firingInAcceptingPlaceIndex;
		if (transition.getSuccessors().stream().anyMatch(mOperand::isAccepting)) {
			firingInAcceptingPlaceIndex = mFireSequenceIndex;
		} else {
			firingInAcceptingPlaceIndex = predecessor.getLastIndexOfShootingAcceptingStateInFireSequence();
		}
		return new MarkingOfFireSequence<>(predecessor.getMarking().fireTransition(transition),
				predecessor.getHondaMarkingsOfFireSequence(), firingInAcceptingPlaceIndex);
	}

	@Override
	boolean checkForAcceptingConditions() {
		for (final Pair<MarkingOfFireSequence<LETTER, PLACE>, Integer> markingAndHondaIndex : containsLoopingFiresequence(
				mFireSequenceTreeMarkings)) {
			if (markingAndHondaIndex.getFirst()
					.getLastIndexOfShootingAcceptingStateInFireSequence() >= markingAndHondaIndex.getSecond()) {
				return true;
			}
			// any nonaccepting firing sequence stuck in a loop is disregarded
			mFireSequenceTreeMarkings.remove(markingAndHondaIndex.getFirst());
		}
		return false;
	}

	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of accepts");
		}
		final boolean resultAutomata =
				(new de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts<>(mServices,
						(new BuchiPetriNet2FiniteAutomaton<>(mServices, stateFactory,
								(IBlackWhiteStateFactory<PLACE>) stateFactory, mOperand)).getResult(),
						mLassoWord)).getResult();
		final boolean correct = mResult == resultAutomata;

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of accepts");
		}

		return correct;
	}
}
