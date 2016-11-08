/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Nested word automaton with on-demand construction for letters and states.
 * Supports all methods that are required by
 * {@link NestedWordAutomatonReachableStates} which is able to transform
 * objects of this class into an {@link IDoubleDeckerAutomaton}.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class NestedWordAutomatonOnDemandStateAndLetter<LETTER, STATE>
		implements INestedWordAutomatonSimple<LETTER, STATE> {
	
	protected final AutomataLibraryServices mServices;
	
	protected final NestedWordAutomatonCache<LETTER, STATE> mCache;
	
	protected final Set<LETTER> mInternalAlphabet;
	protected final Set<LETTER> mCallAlphabet;
	protected final Set<LETTER> mReturnAlphabet;
	
	protected boolean mInitialStateHaveBeenConstructed;
	
	private final Set<STATE> mInternalSuccessorsConstruted;
	private final Set<STATE> mCallSuccessorsConstruted;
	private final HashRelation<STATE, STATE> mReturnSuccessorsConstruted;
	
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 */
	public NestedWordAutomatonOnDemandStateAndLetter(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory) {
		mServices = services;
		mInternalSuccessorsConstruted = new HashSet<>();
		mCallSuccessorsConstruted = new HashSet<>();
		mReturnSuccessorsConstruted = new HashRelation<>();
		mInternalAlphabet = new HashSet<>();
		mCallAlphabet = new HashSet<>();
		mReturnAlphabet = new HashSet<>();
		mCache = new NestedWordAutomatonCache<>(mServices, mInternalAlphabet, mCallAlphabet, mReturnAlphabet,
				stateFactory);
	}
	
	protected abstract void constructInitialStates() throws AutomataOperationCanceledException;
	
	protected abstract void constructInternalSuccessors(STATE state);
	
	protected abstract void constructCallSuccessors(STATE state);
	
	protected abstract void constructReturnSuccessors(STATE lin, STATE hier);
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#getInternalAlphabet()
	 */
	@Override
	public Set<LETTER> getInternalAlphabet() {
		return mCache.getInternalAlphabet();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#getCallAlphabet()
	 */
	@Override
	public Set<LETTER> getCallAlphabet() {
		return mCache.getCallAlphabet();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#getReturnAlphabet()
	 */
	@Override
	public Set<LETTER> getReturnAlphabet() {
		return mCache.getReturnAlphabet();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#getEmptyStackState()
	 */
	@Override
	public STATE getEmptyStackState() {
		return mCache.getEmptyStackState();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#size()
	 */
	@Override
	public int size() {
		return mCache.size();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#getAlphabet()
	 */
	@Override
	public Set<LETTER> getAlphabet() {
		return mCache.getAlphabet();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#getInitialStates()
	 */
	@Override
	public Collection<STATE> getInitialStates() {
		if (!mInitialStateHaveBeenConstructed) {
			throw new AssertionError("initial states not constructed");
		}
		return mCache.getInitialStates();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#lettersInternal(
	 *      java.lang.Object)
	 */
	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		throw new UnsupportedOperationException();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#lettersCall(
	 * java.lang.Object)
	 */
	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		throw new UnsupportedOperationException();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#lettersReturn(
	 * java.lang.Object)
	 */
	@Override
	public Set<LETTER> lettersReturn(final STATE state) {
		throw new UnsupportedOperationException();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#internalSuccessors(
	 * java.lang.Object,
	 *      java.lang.Object)
	 */
	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		throw new UnsupportedOperationException();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#internalSuccessors(
	 * java.lang.Object)
	 */
	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		if (!mInternalSuccessorsConstruted.contains(state)) {
			constructInternalSuccessors(state);
			mInternalSuccessorsConstruted.add(state);
		}
		return mCache.internalSuccessors(state);
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#callSuccessors(
	 * java.lang.Object,
	 *      java.lang.Object)
	 */
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		throw new UnsupportedOperationException();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#callSuccessors(
	 * java.lang.Object)
	 */
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		if (!mCallSuccessorsConstruted.contains(state)) {
			constructCallSuccessors(state);
			mCallSuccessorsConstruted.add(state);
		}
		return mCache.callSuccessors(state);
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#returnSuccessors(
	 * java.lang.Object,
	 *      java.lang.Object, java.lang.Object)
	 */
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		throw new UnsupportedOperationException();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#returnSuccessorsGivenHier(
	 * java.lang.Object,
	 *      java.lang.Object)
	 */
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		if (!mReturnSuccessorsConstruted.containsPair(state, hier)) {
			constructReturnSuccessors(state, hier);
			mReturnSuccessorsConstruted.addPair(state, hier);
		}
		return mCache.returnSuccessorsGivenHier(state, hier);
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#sizeInformation()
	 */
	@Override
	public String sizeInformation() {
		return mCache.sizeInformation();
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#isInitial(java.lang.Object)
	 */
	@Override
	public boolean isInitial(final STATE state) {
		return mCache.isInitial(state);
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#isFinal(java.lang.Object)
	 */
	@Override
	public boolean isFinal(final STATE state) {
		return mCache.isFinal(state);
	}
	
	/**
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonCache#getStateFactory()
	 */
	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mCache.getStateFactory();
	}
}
