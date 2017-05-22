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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap4;

/**
 * Takes a {@link INwaSuccessorStateProvider} and acts as a {@link NwaOutgoingLetterAndTransitionAdapter}.
 * Motivation: {@link INwaSuccessorStateProvider} should only be used to defne
 * successors. This class does the caching (avoid that transitions are constructed twice)
 * and the conversion from outgoing successors to outgoing transitions.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Type of objects which can be used as letters of the alphabet.
 * @param <STATE>
 *            Type of objects which can be used as states.
 */
public class NwaOutgoingLetterAndTransitionAdapter<LETTER, STATE> implements INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {
	
	private final INwaSuccessorStateProvider<LETTER, STATE> mNwaSuccessorStateProvider;
	
	private final NestedMap3<STATE, LETTER, STATE, IsContained> mInternalTransitionCache = new NestedMap3<>();
	private final NestedMap2<STATE, LETTER, IsContained> mInternalTransitionBookkeeping = new NestedMap2<>();
	
	private final NestedMap3<STATE, LETTER, STATE, IsContained> mCallTransitionCache = new NestedMap3<>();
	private final NestedMap2<STATE, LETTER, IsContained> mCallTransitionBookkeeping = new NestedMap2<>();

	private final NestedMap4<STATE, STATE, LETTER, STATE, IsContained> mReturnTransitionCache = new NestedMap4<>();
	private final NestedMap3<STATE, STATE, LETTER, IsContained> mReturnTransitionBookkeeping = new NestedMap3<>();
	

	public NwaOutgoingLetterAndTransitionAdapter(final INwaSuccessorStateProvider<LETTER, STATE> nwaSuccessorStateProvider) {
		super();
		mNwaSuccessorStateProvider = nwaSuccessorStateProvider;
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mNwaSuccessorStateProvider.getStateFactory();
	}

	@Override
	public int size() {
		return mNwaSuccessorStateProvider.size();
	}

	@Override
	public String sizeInformation() {
		return mNwaSuccessorStateProvider.sizeInformation();
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mNwaSuccessorStateProvider.getVpAlphabet();
	}

	@Override
	public STATE getEmptyStackState() {
		return mNwaSuccessorStateProvider.getEmptyStackState();
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		return mNwaSuccessorStateProvider.getInitialStates();
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mNwaSuccessorStateProvider.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return mNwaSuccessorStateProvider.isFinal(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state, final LETTER letter) {
		if (mInternalTransitionBookkeeping.get(state, letter) == null) {
			final Collection<STATE> computedSuccs = mNwaSuccessorStateProvider.internalSuccessors(state, letter);
			for (final STATE succ : computedSuccs) {
				mInternalTransitionCache.put(state, letter, succ, IsContained.IsContained);
			}
		}
		return NestedWordAutomataUtils.constructInternalTransitionIteratorFromNestedMap(state, letter, mInternalTransitionCache);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		if (mCallTransitionBookkeeping.get(state, letter) == null) {
			final Collection<STATE> computedSuccs = mNwaSuccessorStateProvider.callSuccessors(state, letter);
			for (final STATE succ : computedSuccs) {
				mCallTransitionCache.put(state, letter, succ, IsContained.IsContained);
			}
		}
		return NestedWordAutomataUtils.constructCallTransitionIteratorFromNestedMap(state, letter, mCallTransitionCache);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier, final LETTER letter) {
		if (mReturnTransitionBookkeeping.get(state, hier, letter) == null) {
			final Collection<STATE> computedSuccs = mNwaSuccessorStateProvider.returnSuccessorsGivenHier(state, hier, letter);
			for (final STATE succ : computedSuccs) {
				mReturnTransitionCache.put(state, hier, letter, succ, IsContained.IsContained);
			}
		}
		return NestedWordAutomataUtils.constructReturnTransitionIteratorFromNestedMap(state, hier, letter, mReturnTransitionCache);
	}


}
