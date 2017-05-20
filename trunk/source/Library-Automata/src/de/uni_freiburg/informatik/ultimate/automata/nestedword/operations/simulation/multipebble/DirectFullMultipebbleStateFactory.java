/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble;

import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble.IFullMultipebbleAuxiliaryGameState.AuxiliaryGameStateType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <STATE>
 *            state type
 */
public class DirectFullMultipebbleStateFactory<STATE>
		extends FullMultipebbleStateFactory<STATE, DirectFullMultipebbleGameState<STATE>> {

	public DirectFullMultipebbleStateFactory(final ISetOfPairs<STATE, ?> initialPartition) {
		super(initialPartition);
	}

	@Override
	public DirectFullMultipebbleGameState<STATE> createSinkStateContent() {
		return new AuxiliaryDirectFullMultipebbleGameState<>(
				AuxiliaryGameStateType.DEFAULT_SINK_FOR_AUTOMATA_OPERATIONS);
	}

	@Override
	public DirectFullMultipebbleGameState<STATE> createEmptyStackState() {
		return new AuxiliaryDirectFullMultipebbleGameState<>(AuxiliaryGameStateType.EMPTY_STACK);
	}

	@Override
	protected DirectFullMultipebbleGameState<STATE> constructSpoilerWinningSink() {
		return new AuxiliaryDirectFullMultipebbleGameState<>(AuxiliaryGameStateType.SPOILER_WINNING_SINK);
	}

	@Override
	protected <LETTER> DirectFullMultipebbleGameState<STATE> computeSuccessorsInternalGivenSpoilerSucc(
			final DoubleDecker<STATE> spoilerSucc, final DirectFullMultipebbleGameState<STATE> gs, final LETTER letter,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa) {
		final boolean spoilerSuccIsFinal = nwa.isFinal(spoilerSucc.getUp());
		final HashRelation<STATE, STATE> duplicatorSuccStates = new HashRelation<>();
		for (final Entry<STATE, STATE> doubleDecker : gs.getDuplicatorDoubleDeckers().entrySet()) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : nwa.internalSuccessors(doubleDecker.getValue(),
					letter)) {
				final DoubleDecker<STATE> duplicatorSucc = new DoubleDecker<>(doubleDecker.getKey(), trans.getSucc());
				if (spoilerSucc.equals(duplicatorSucc)) {
					// duplicator succs contains spoiler succ, hence spoiler cannot win
					return null;
				}
				if ((!spoilerSuccIsFinal || nwa.isFinal(duplicatorSucc.getUp()))
						&& isSimulationCandidate(spoilerSucc.getUp(), duplicatorSucc.getUp())) {
					duplicatorSuccStates.addPair(duplicatorSucc.getDown(), duplicatorSucc.getUp());
				}
			}
		}
		if (duplicatorSuccStates.isEmpty()) {
			return mSpoilerWinningSink;
		}
		return new DirectFullMultipebbleGameState<>(spoilerSucc, duplicatorSuccStates);
	}

	@Override
	protected <LETTER> DirectFullMultipebbleGameState<STATE> computeSuccessorsCallGivenSpoilerSucc(
			final DoubleDecker<STATE> spoilerSucc, final DirectFullMultipebbleGameState<STATE> gs, final LETTER letter,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa) {
		final boolean spoilerSuccIsFinal = nwa.isFinal(spoilerSucc.getUp());
		final HashRelation<STATE, STATE> duplicatorSuccStates = new HashRelation<>();
		for (final Entry<STATE, STATE> doubleDecker : gs.getDuplicatorDoubleDeckers().entrySet()) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : nwa.callSuccessors(doubleDecker.getValue(),
					letter)) {
				final DoubleDecker<STATE> duplicatorSucc = new DoubleDecker<>(doubleDecker.getValue(), trans.getSucc());
				if (spoilerSucc.equals(duplicatorSucc)) {
					// duplicator succs contains spoiler succ, hence spoiler cannot win
					return null;
				}
				if ((!spoilerSuccIsFinal || nwa.isFinal(duplicatorSucc.getUp()))
						&& isSimulationCandidate(spoilerSucc.getUp(), duplicatorSucc.getUp())) {
					duplicatorSuccStates.addPair(duplicatorSucc.getDown(), duplicatorSucc.getUp());
				}
			}
		}
		if (duplicatorSuccStates.isEmpty()) {
			return mSpoilerWinningSink;
		}
		return new DirectFullMultipebbleGameState<>(spoilerSucc, duplicatorSuccStates);
	}

	@Override
	protected <LETTER> DirectFullMultipebbleGameState<STATE> computeSuccessorsReturnGivenSpoilerSucc(
			final DoubleDecker<STATE> spoilerSucc, final DirectFullMultipebbleGameState<STATE> gs,
			final DirectFullMultipebbleGameState<STATE> hier, final LETTER letter,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa) {
		final boolean spoilerSuccIsFinal = nwa.isFinal(spoilerSucc.getUp());
		final HashRelation<STATE, STATE> duplicatorSuccStates = new HashRelation<>();
		for (final Entry<STATE, STATE> hierDoubleDecker : hier.getDuplicatorDoubleDeckers().entrySet()) {
			for (final STATE up : gs.getDuplicatorDoubleDeckers().getImage(hierDoubleDecker.getValue())) {
				for (final OutgoingReturnTransition<LETTER, STATE> trans : nwa.returnSuccessors(up,
						hierDoubleDecker.getValue(), letter)) {
					final DoubleDecker<STATE> duplicatorSucc =
							new DoubleDecker<>(hierDoubleDecker.getKey(), trans.getSucc());
					if (spoilerSucc.equals(duplicatorSucc)) {
						// duplicator succs contains spoiler succ, hence spoiler cannot win
						return null;
					}
					if ((!spoilerSuccIsFinal || nwa.isFinal(duplicatorSucc.getUp()))
							&& isSimulationCandidate(spoilerSucc.getUp(), duplicatorSucc.getUp())) {
						duplicatorSuccStates.addPair(duplicatorSucc.getDown(), duplicatorSucc.getUp());
					}
				}
			}
		}
		if (duplicatorSuccStates.isEmpty()) {
			return mSpoilerWinningSink;
		}
		return new DirectFullMultipebbleGameState<>(spoilerSucc, duplicatorSuccStates);
	}

	@Override
	public <LETTER> boolean isImmediatelyWinningForSpoiler(final STATE q0, final STATE q1,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) {
		return operand.isFinal(q0) && !operand.isFinal(q1);
	}

	@Override
	public <LETTER> DirectFullMultipebbleGameState<STATE> constructInitialState(final STATE q0, final STATE q1,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) {
		if (isImmediatelyWinningForSpoiler(q0, q1, operand)) {
			throw new AssertionError("cannot construct state that is winning for spoiler");
		}
		final HashRelation<STATE, STATE> duplicatorDoubleDeckers = new HashRelation<>();
		duplicatorDoubleDeckers.addPair(operand.getEmptyStackState(), q1);
		return new DirectFullMultipebbleGameState<>(new DoubleDecker<>(operand.getEmptyStackState(), q0),
				duplicatorDoubleDeckers);
	}

	public static class AuxiliaryDirectFullMultipebbleGameState<STATE> extends DirectFullMultipebbleGameState<STATE>
			implements IFullMultipebbleAuxiliaryGameState {

		private final AuxiliaryGameStateType mAuxiliaryGameStateType;

		public AuxiliaryDirectFullMultipebbleGameState(final AuxiliaryGameStateType auxiliaryGameStateType) {
			super(null, null);
			mAuxiliaryGameStateType = auxiliaryGameStateType;
		}

		@Override
		public HashRelation<STATE, STATE> getDuplicatorDoubleDeckers() {
			throw new UnsupportedOperationException();
		}

		@Override
		public int getNumberOfDoubleDeckerPebbles() {
			return 0;
		}

		@Override
		public boolean isAccepting() {
			return true;
		}

		@Override
		public String toString() {
			return getAuxiliaryGameStateType().toString();
		}

		@Override
		public AuxiliaryGameStateType getAuxiliaryGameStateType() {
			return mAuxiliaryGameStateType;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = super.hashCode();
			result = prime * result + ((mAuxiliaryGameStateType == null) ? 0 : mAuxiliaryGameStateType.hashCode());
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (!super.equals(obj)) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final AuxiliaryDirectFullMultipebbleGameState<?> other = (AuxiliaryDirectFullMultipebbleGameState<?>) obj;
			if (mAuxiliaryGameStateType != other.mAuxiliaryGameStateType) {
				return false;
			}
			return true;
		}

	}
}
