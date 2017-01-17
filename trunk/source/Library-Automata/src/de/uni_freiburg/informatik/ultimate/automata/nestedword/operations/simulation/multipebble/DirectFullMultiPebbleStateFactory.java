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

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 */
public class DirectFullMultiPebbleStateFactory<STATE> extends FullMultipebbleStateFactory<STATE, DirectFullMultipebbleGameState<STATE>>  {

	@Override
	public DirectFullMultipebbleGameState<STATE> createSinkStateContent() {
		return new AuxiliaryDirectFullMultipebbleGameState<>("sink");
	}

	@Override
	public DirectFullMultipebbleGameState<STATE> createEmptyStackState() {
		return new AuxiliaryDirectFullMultipebbleGameState<>("EmptyStack");
	}
	
	
	
	private <LETTER> HashRelation<STATE, STATE> computeDuplicatorSuccessorsInternal(final DoubleDecker<STATE> spoilerSucc, final DirectFullMultipebbleGameState<STATE> gs, 
			final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		final boolean spoilerSuccIsFinal = nwa.isFinal(spoilerSucc.getUp());
		final HashRelation<STATE, STATE> result = new HashRelation<>();
		for (final Entry<STATE, STATE> doubleDecker : gs.getDuplicatorDoubleDeckers().entrySet()) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : nwa.internalSuccessors(doubleDecker.getValue(), letter)) {
				final DoubleDecker<STATE> duplicatorSucc = new DoubleDecker<>(doubleDecker.getKey(), trans.getSucc());
				if (spoilerSucc.equals(duplicatorSucc)) {
					// duplicator succs contains spoiler succ, hence spoiler cannot win 
					return null;
				}
				if (!spoilerSuccIsFinal || nwa.isFinal(duplicatorSucc.getUp())) {
					result.addPair(duplicatorSucc.getDown(), duplicatorSucc.getUp());
				}
			}
		}
		return result;
	}
	
	@Override
	public <LETTER> List<DirectFullMultipebbleGameState<STATE>> computeSuccessorsInternal(final DirectFullMultipebbleGameState<STATE> gs, 
			final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		final List<DirectFullMultipebbleGameState<STATE>> result = new ArrayList<>();
		for (final DoubleDecker<STATE> spoilerSucc : gs.computeSpoilerSuccessorsInternal(letter, nwa)) {
			final HashRelation<STATE, STATE> duplicatorSucc = computeDuplicatorSuccessorsInternal(spoilerSucc, gs, letter, nwa);
			if (duplicatorSucc != null) {
				result.add(new DirectFullMultipebbleGameState<>(spoilerSucc, duplicatorSucc));
			}
		}
		return result;
	}
	
	private <LETTER> HashRelation<STATE, STATE> computeDuplicatorSuccessorsCall(final DoubleDecker<STATE> spoilerSucc, final DirectFullMultipebbleGameState<STATE> gs, 
			final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		final boolean spoilerSuccIsFinal = nwa.isFinal(spoilerSucc.getUp());
		final HashRelation<STATE, STATE> result = new HashRelation<>();
		for (final Entry<STATE, STATE> doubleDecker : gs.getDuplicatorDoubleDeckers().entrySet()) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : nwa.callSuccessors(doubleDecker.getValue(), letter)) {
				final DoubleDecker<STATE> duplicatorSucc = new DoubleDecker<>(doubleDecker.getValue(), trans.getSucc());
				if (spoilerSucc.equals(duplicatorSucc)) {
					// duplicator succs contains spoiler succ, hence spoiler cannot win 
					return null;
				}
				if (!spoilerSuccIsFinal || nwa.isFinal(duplicatorSucc.getUp())) {
					result.addPair(duplicatorSucc.getDown(), duplicatorSucc.getUp());
				}
			}
		}
		return result;
	}
	
	@Override
	public <LETTER> List<DirectFullMultipebbleGameState<STATE>> computeSuccessorsCall(final DirectFullMultipebbleGameState<STATE> gs, 
			final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		final List<DirectFullMultipebbleGameState<STATE>> result = new ArrayList<>();
		for (final DoubleDecker<STATE> spoilerSucc : gs.computeSpoilerSuccessorsCall(letter, nwa)) {
			final HashRelation<STATE, STATE> duplicatorSucc = computeDuplicatorSuccessorsCall(spoilerSucc, gs, letter, nwa);
			if (duplicatorSucc != null) {
				result.add(new DirectFullMultipebbleGameState<>(spoilerSucc, duplicatorSucc));
			}
		}
		return result;
	}
	
	private <LETTER> HashRelation<STATE, STATE> computeDuplicatorSuccessorsReturn(final DoubleDecker<STATE> spoilerSucc, final DirectFullMultipebbleGameState<STATE> gs, 
			final HashRelation<STATE, STATE> hier, final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		final boolean spoilerSuccIsFinal = nwa.isFinal(spoilerSucc.getUp());
		final HashRelation<STATE, STATE> result = new HashRelation<>();
		for (final Entry<STATE, STATE> hierDoubleDecker : hier.entrySet()) {
			for (final STATE up : gs.getDuplicatorDoubleDeckers().getImage(hierDoubleDecker.getValue())) {
				for (final OutgoingReturnTransition<LETTER, STATE> trans : nwa.returnSuccessors(up, hierDoubleDecker.getValue(), letter)) {
					final DoubleDecker<STATE> duplicatorSucc = new DoubleDecker<>(hierDoubleDecker.getKey(), trans.getSucc());
					if (spoilerSucc.equals(duplicatorSucc)) {
						// duplicator succs contains spoiler succ, hence spoiler cannot win 
						return null;
					}
					if (!spoilerSuccIsFinal || nwa.isFinal(duplicatorSucc.getUp())) {
						result.addPair(duplicatorSucc.getDown(), duplicatorSucc.getUp());
					}
				}
			}
			
		}
		return result;
	}
	
	@Override
	public <LETTER> List<DirectFullMultipebbleGameState<STATE>> computeSuccessorsReturn(final DirectFullMultipebbleGameState<STATE> gs, 
			final DirectFullMultipebbleGameState<STATE> hier, final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		final List<DirectFullMultipebbleGameState<STATE>> result = new ArrayList<>();
		for (final DoubleDecker<STATE> spoilerSucc : gs.computeSpoilerSuccessorsReturn(hier.getSpoilerDoubleDecker(), letter, nwa)) {
			final HashRelation<STATE, STATE> duplicatorSucc = computeDuplicatorSuccessorsReturn(spoilerSucc, gs, hier.getDuplicatorDoubleDeckers(), letter, nwa);
			if (duplicatorSucc != null) {
				result.add(new DirectFullMultipebbleGameState<>(spoilerSucc, duplicatorSucc));
			}
		}
		return result;
	}
	
	
	
	
	
	
	public static class AuxiliaryDirectFullMultipebbleGameState<STATE> extends DirectFullMultipebbleGameState<STATE> {

		private final String mDebugIdentifier;

		public AuxiliaryDirectFullMultipebbleGameState(final String debugIdentifier) {
			super(null, null);
			mDebugIdentifier = debugIdentifier;
		}

		@Override
		public HashRelation<STATE, STATE> getDuplicatorDoubleDeckers() {
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
		return operand.isFinal(q0) && !operand.isFinal(q1);
	}

	@Override
	public <LETTER> DirectFullMultipebbleGameState<STATE> constructInitialState(final STATE q0, final STATE q1,
			final INestedWordAutomatonSimple<LETTER, STATE> operand) {
		if (isImmediatelyWinningForSpoiler(q0, q1, operand)) {
			throw new AssertionError("cannot construct state that is winning for spoiler");
		}
		final HashRelation<STATE, STATE> duplicatorDoubleDeckers = new HashRelation<>();
		duplicatorDoubleDeckers.addPair(operand.getEmptyStackState(), q1);
		return new DirectFullMultipebbleGameState<>(new DoubleDecker<STATE>(operand.getEmptyStackState(), q0), duplicatorDoubleDeckers);
	}
	

	
}
