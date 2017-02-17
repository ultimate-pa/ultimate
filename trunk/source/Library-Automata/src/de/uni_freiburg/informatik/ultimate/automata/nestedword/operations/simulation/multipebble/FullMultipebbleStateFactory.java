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
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
/**
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 * @param <GS>
 */
public abstract class FullMultipebbleStateFactory<STATE, GS extends FullMultipebbleGameState<STATE>>
		implements ISinkStateFactory<GS>, IEmptyStackStateFactory<GS> {
	
	private int mMaxNumberOfDoubleDeckerPebbles = 0;
	protected final GS mSpoilerWinningSink;
	
	private final ISetOfPairs<STATE, ?> mInitialPartition;

	public FullMultipebbleStateFactory(final ISetOfPairs<STATE, ?> initialPartition) {
		super();
		mInitialPartition = initialPartition;
		mSpoilerWinningSink = constructSpoilerWinningSink();
	}
	
	protected boolean isInInitialPartition(final STATE spoilerState, final STATE duplicatorState) {
		return mInitialPartition.containsPair(spoilerState, duplicatorState);
	}

	
	protected abstract <LETTER> GS constructSpoilerWinningSink();
	
	protected abstract <LETTER> GS computeSuccessorsInternalGivenSpoilerSucc(DoubleDecker<STATE> spoilerSucc, GS gs, final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa);
	protected abstract <LETTER> GS computeSuccessorsCallGivenSpoilerSucc(DoubleDecker<STATE> spoilerSucc, GS gs, final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa);
	protected abstract <LETTER> GS computeSuccessorsReturnGivenSpoilerSucc(DoubleDecker<STATE> spoilerSucc, GS gs, final GS hier, final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa);


	public abstract <LETTER> boolean isImmediatelyWinningForSpoiler(final STATE q0, final STATE q1, final INestedWordAutomatonSimple<LETTER, STATE> operand);


	public abstract <LETTER> GS constructInitialState(STATE q0, STATE q1, INestedWordAutomatonSimple<LETTER, STATE> operand);
	
	
	public final <LETTER> List<GS> computeSuccessorsInternal(final GS gs,
			final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		if (IFullMultipebbleAuxiliaryGameState.isDuplicatorWinningSink(gs)) {
			return Collections.emptyList();
		}
		final List<GS> result = new ArrayList<>();
		for (final DoubleDecker<STATE> spoilerSucc : gs.computeSpoilerSuccessorsInternal(letter, nwa)) {
			final GS duplicatorSucc = computeSuccessorsInternalGivenSpoilerSucc(spoilerSucc, gs, letter, nwa);
			if (duplicatorSucc != null) {
				mMaxNumberOfDoubleDeckerPebbles = Math.max(mMaxNumberOfDoubleDeckerPebbles, duplicatorSucc.getNumberOfDoubleDeckerPebbles());
				result.add(duplicatorSucc);
			}
		}
		return result;
	}


	public final <LETTER> List<GS> computeSuccessorsCall(final GS gs,
			final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		if (IFullMultipebbleAuxiliaryGameState.isDuplicatorWinningSink(gs)) {
			return Collections.emptyList();
		}
		final List<GS> result = new ArrayList<>();
		for (final DoubleDecker<STATE> spoilerSucc : gs.computeSpoilerSuccessorsCall(letter, nwa)) {
			final GS duplicatorSucc = computeSuccessorsCallGivenSpoilerSucc(spoilerSucc, gs, letter, nwa);
			if (duplicatorSucc != null) {
				mMaxNumberOfDoubleDeckerPebbles = Math.max(mMaxNumberOfDoubleDeckerPebbles, duplicatorSucc.getNumberOfDoubleDeckerPebbles());
				result.add(duplicatorSucc);
			}
		}
		return result;
	}
	
	
	public final <LETTER> List<GS> computeSuccessorsReturn(final GS gs,
			final GS hier, final LETTER letter, final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		if (IFullMultipebbleAuxiliaryGameState.isDuplicatorWinningSink(gs)) {
			return Collections.emptyList();
		}
		final List<GS> result = new ArrayList<>();
		for (final DoubleDecker<STATE> spoilerSucc : gs.computeSpoilerSuccessorsReturn(hier.getSpoilerDoubleDecker(), letter, nwa)) {
			final GS duplicatorSucc = computeSuccessorsReturnGivenSpoilerSucc(spoilerSucc, gs, hier, letter, nwa);
			if (duplicatorSucc != null) {
				mMaxNumberOfDoubleDeckerPebbles = Math.max(mMaxNumberOfDoubleDeckerPebbles, duplicatorSucc.getNumberOfDoubleDeckerPebbles());
				result.add(duplicatorSucc);
			}
		}
		return result;
	}


	public int getMaxNumberOfDoubleDeckerPebbles() {
		return mMaxNumberOfDoubleDeckerPebbles;
	}

}