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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 */
public class DelayedFullMultipebbleStateFactory<STATE> extends FullMultipebbleStateFactory<STATE, DelayedFullMultipebbleGameState<STATE>>  {

	@Override
	public DelayedFullMultipebbleGameState<STATE> createSinkStateContent() {
		return new AuxiliaryDelayedFullMultipebbleGameState<>("sink");
	}

	@Override
	public DelayedFullMultipebbleGameState<STATE> createEmptyStackState() {
		return new AuxiliaryDelayedFullMultipebbleGameState<>("EmptyStack");
	}
	
	
	
	@Override
	protected <LETTER> DelayedFullMultipebbleGameState<STATE> computeSuccessorsInternalGivenSpoilerSucc(final DoubleDecker<STATE> spoilerSucc, final DelayedFullMultipebbleGameState<STATE> gs, 
			final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		final boolean spoilerSuccIsFinal = nwa.isFinal(spoilerSucc.getUp());
		final NestedMap2<STATE, STATE, Boolean> duplicatorSuccStates = new NestedMap2<>();
		for (final Triple<STATE, STATE, Boolean> doubleDecker : gs.getDuplicatorDoubleDeckers().entrySet()) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : nwa.internalSuccessors(doubleDecker.getSecond(), letter)) {
				final DoubleDecker<STATE> duplicatorSucc = new DoubleDecker<>(doubleDecker.getFirst(), trans.getSucc());
				final boolean succDuplicatorObligationBit = computeSuccDuplicatorObligationBit(spoilerSuccIsFinal, doubleDecker.getThird(), duplicatorSucc.getUp(), nwa);
				if (!succDuplicatorObligationBit && spoilerSucc.equals(duplicatorSucc)) {
					// duplicator succs contains spoiler succ, hence spoiler cannot win 
					return null;
				}
				if (duplicatorSuccStates.get(duplicatorSucc.getDown(), duplicatorSucc.getUp()) == Boolean.FALSE) {
					// do nothing, DoubleDecker without obligation already contained
				} else {
					duplicatorSuccStates.put(duplicatorSucc.getDown(), duplicatorSucc.getUp(), succDuplicatorObligationBit);
				}
			}
		}
		return new DelayedFullMultipebbleGameState<>(spoilerSucc, duplicatorSuccStates);
	}
	

	


	@Override
	protected <LETTER> DelayedFullMultipebbleGameState<STATE> computeSuccessorsCallGivenSpoilerSucc(final DoubleDecker<STATE> spoilerSucc, final DelayedFullMultipebbleGameState<STATE> gs, 
			final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		final boolean spoilerSuccIsFinal = nwa.isFinal(spoilerSucc.getUp());
		final NestedMap2<STATE, STATE, Boolean> duplicatorSuccStates = new NestedMap2<>();
		for (final Triple<STATE, STATE, Boolean> doubleDecker : gs.getDuplicatorDoubleDeckers().entrySet()) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : nwa.callSuccessors(doubleDecker.getSecond(), letter)) {
				final DoubleDecker<STATE> duplicatorSucc = new DoubleDecker<>(doubleDecker.getSecond(), trans.getSucc());
				final boolean succDuplicatorObligationBit = computeSuccDuplicatorObligationBit(spoilerSuccIsFinal, doubleDecker.getThird(), duplicatorSucc.getUp(), nwa);
				if (!succDuplicatorObligationBit && spoilerSucc.equals(duplicatorSucc)) {
					// duplicator succs contains spoiler succ, hence spoiler cannot win 
					return null;
				}
				if (duplicatorSuccStates.get(duplicatorSucc.getDown(), duplicatorSucc.getUp()) == Boolean.FALSE) {
					// do nothing, DoubleDecker without obligation already contained
				} else {
					duplicatorSuccStates.put(duplicatorSucc.getDown(), duplicatorSucc.getUp(), succDuplicatorObligationBit);
				}
			}
		}
		return new DelayedFullMultipebbleGameState<>(spoilerSucc, duplicatorSuccStates);
	}
	

	
	@Override
	protected <LETTER> DelayedFullMultipebbleGameState<STATE> computeSuccessorsReturnGivenSpoilerSucc(final DoubleDecker<STATE> spoilerSucc, final DelayedFullMultipebbleGameState<STATE> gs, 
			final DelayedFullMultipebbleGameState<STATE> hier, final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		final boolean spoilerSuccIsFinal = nwa.isFinal(spoilerSucc.getUp());
		final NestedMap2<STATE, STATE, Boolean> duplicatorSuccStates = new NestedMap2<>();
		for (final Triple<STATE, STATE, Boolean> hierDoubleDecker : hier.getDuplicatorDoubleDeckers().entrySet()) {
			for (final Entry<STATE, Boolean> entry : gs.getDuplicatorDoubleDeckers().get(hierDoubleDecker.getSecond()).entrySet()) {
				for (final OutgoingReturnTransition<LETTER, STATE> trans : nwa.returnSuccessors(entry.getKey(), hierDoubleDecker.getSecond(), letter)) {
					final DoubleDecker<STATE> duplicatorSucc = new DoubleDecker<>(hierDoubleDecker.getFirst(), trans.getSucc());
					
					final boolean succDuplicatorObligationBit = computeSuccDuplicatorObligationBit(spoilerSuccIsFinal, entry.getValue(), duplicatorSucc.getUp(), nwa);
					if (!succDuplicatorObligationBit && spoilerSucc.equals(duplicatorSucc)) {
						// duplicator succs contains spoiler succ, hence spoiler cannot win 
						return null;
					}
					if (duplicatorSuccStates.get(duplicatorSucc.getDown(), duplicatorSucc.getUp()) == Boolean.FALSE) {
						// do nothing, DoubleDecker without obligation already contained
					} else {
						duplicatorSuccStates.put(duplicatorSucc.getDown(), duplicatorSucc.getUp(), succDuplicatorObligationBit);
					}
				}
			}
			
		}
		return new DelayedFullMultipebbleGameState<>(spoilerSucc, duplicatorSuccStates);
	}
	
	
	
	private <LETTER> boolean computeSuccDuplicatorObligationBit(final boolean spoilerSuccIsFinal, 
			final Boolean predecessorDuplicatorObligationBit, final STATE duplicatorSucc,
			final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		return (spoilerSuccIsFinal || predecessorDuplicatorObligationBit) && ! nwa.isFinal(duplicatorSucc);
		
	}
	
	
	
	
	public static class AuxiliaryDelayedFullMultipebbleGameState<STATE> extends DelayedFullMultipebbleGameState<STATE> {

		private final String mDebugIdentifier;

		public AuxiliaryDelayedFullMultipebbleGameState(final String debugIdentifier) {
			super(null, null);
			mDebugIdentifier = debugIdentifier;
		}

		@Override
		public NestedMap2<STATE, STATE, Boolean> getDuplicatorDoubleDeckers() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isAccepting() {
			throw new UnsupportedOperationException();
		}

		@Override
		public String toString() {
			return mDebugIdentifier;
		}
		
		
		
		
	}






	@Override
	public <LETTER> boolean isImmediatelyWinningForSpoiler(final STATE q0, final STATE q1,
			final INestedWordAutomatonSimple<LETTER, STATE> operand) {
		return false;
	}

	@Override
	public <LETTER> DelayedFullMultipebbleGameState<STATE> constructInitialState(final STATE q0, final STATE q1,
			final INestedWordAutomatonSimple<LETTER, STATE> operand) {
		final NestedMap2<STATE, STATE, Boolean> duplicatorDoubleDeckers = new NestedMap2<>();
		final boolean duplicatorObligationBit = operand.isFinal(q0) && ! operand.isFinal(q1);
		duplicatorDoubleDeckers.put(operand.getEmptyStackState(), q1, duplicatorObligationBit);
		return new DelayedFullMultipebbleGameState<>(new DoubleDecker<STATE>(operand.getEmptyStackState(), q0), duplicatorDoubleDeckers);
	}
	

	
}
