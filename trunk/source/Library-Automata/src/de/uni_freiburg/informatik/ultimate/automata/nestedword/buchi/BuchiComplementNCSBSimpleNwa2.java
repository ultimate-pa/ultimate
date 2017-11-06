/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.SetOfStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaSuccessorStateProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.NwaToBuchiWrapper;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement.BuchiNwaComplement;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement.NCSB;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement.StateNwaNCSB;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntIterator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementNcsbStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Buchi Complementation based on the algorithm proposed by Frantisek Blahoudek and Jan Stejcek. This complementation is
 * only sound for a special class of automata whose working title is <i>TABA</i> (termination analysis Büchi automata).
 * 
 * @author Yong Li (liyong@ios.ac.cn)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class BuchiComplementNCSBSimpleNwa2<LETTER, STATE> implements INwaSuccessorStateProvider<LETTER, STATE> {

	private final AutomataLibraryServices mServices;
	
	private final SetOfStates<STATE> mSetOfStates;

	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;

	private final IBuchiComplementNcsbStateFactory<STATE> mStateFactory;
	
	private final StateWithRankInfo<STATE> mEmptyStackStateWri;

	private final BuchiNwaComplement mComplementBuchi; 
//	private final Map<Integer, LETTER> mIdLetterMap;
	private final Map<LETTER, Integer> mLetterIdMap;
	private final Map<Integer, STATE> mIdStateMap;
	private final Map<STATE, Integer> mStateIdMap;

	private final NwaToBuchiWrapper<LETTER, STATE> mOperandBuchi;
	private final Map<LevelRankingState<LETTER, STATE>, STATE> mDet2res = new HashMap<>();
	private final Map<Integer, LevelRankingState<LETTER, STATE>> mInt2LevelRanks = new HashMap<>();
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public BuchiComplementNCSBSimpleNwa2(final AutomataLibraryServices services,
			final IBuchiComplementNcsbStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		mServices = services;
		mOperand = operand;
		mStateFactory = stateFactory;
		mSetOfStates = new SetOfStates<>(mStateFactory.createEmptyStackState());
//		mIdLetterMap = new HashMap<>();
		mIdStateMap = new HashMap<>();
		mStateIdMap = new HashMap<>();
		
		int id = 0;
		mLetterIdMap = new HashMap<>();
		// call alphabet
		VpAlphabet<LETTER> vp = operand.getVpAlphabet();

		IntSet callAlphabet = UtilIntSet.newIntSet();
		for(LETTER letter : vp.getCallAlphabet()) {
			mLetterIdMap.put(letter, id);
			callAlphabet.set(id);
			id ++;
		}
		IntSet internalAlphabet = UtilIntSet.newIntSet();
		for(LETTER letter : vp.getInternalAlphabet()) {
			mLetterIdMap.put(letter, id);
			internalAlphabet.set(id);
			id ++;
		}
		IntSet returnAlphabet = UtilIntSet.newIntSet();
		for(LETTER letter : vp.getReturnAlphabet()) {
			mLetterIdMap.put(letter, id);
			returnAlphabet.set(id);
			id ++;
		}

		mEmptyStackStateWri = new StateWithRankInfo<>(mSetOfStates.getEmptyStackState());
		mOperandBuchi = new NwaToBuchiWrapper<LETTER, STATE>(callAlphabet, internalAlphabet, returnAlphabet, mLetterIdMap, operand);
		mComplementBuchi = new BuchiNwaComplement(mOperandBuchi);
		constructInitialState();
	}
	
	

	private void constructInitialState() {
		IntSet initials = mComplementBuchi.getInitialStates();
		IntIterator iter = initials.iterator();
		while(iter.hasNext()) {
			int sId = iter.next();
			getOrAdd(true, sId);
		}
	}
	
	protected STATE getRelatedSTATE(int sId) {
		LevelRankingState<LETTER, STATE> lvlrk = constructLevelRankingState(sId);
		STATE resState = mStateFactory.buchiComplementNcsb(lvlrk);
		mDet2res.put(lvlrk, resState);
		return resState;
	}
	private StateWithRankInfo<STATE> getStackState(int downState) {
		StateWithRankInfo<STATE> stackState = null;
		if(downState == DoubleDecker.EMPTY_DOWN_STATE) {
			stackState = mEmptyStackStateWri;
		}else {
			stackState = new StateWithRankInfo<STATE>(mOperandBuchi.getNwaSTATE(downState));
		}
		return stackState;
	}
	protected LevelRankingState<LETTER, STATE> constructLevelRankingState(int sid) {
		LevelRankingState<LETTER, STATE> lvlrk = mInt2LevelRanks.get(sid);
		if(lvlrk != null) return lvlrk;
		
		StateNwaNCSB state = (StateNwaNCSB) mComplementBuchi.getState(sid);
		NCSB ncsb = state.getNCSB();

		lvlrk = new LevelRankingState<>(mOperand);
		IntSet B = ncsb.getBSet();
		// N
		IntSet temp = ncsb.getNSet();
		addLevelRankingState(lvlrk, temp, 3, false);
		// C\B
		temp = ncsb.copyCSet();
		temp.andNot(B);
		addLevelRankingState(lvlrk, temp, 2, false);
		// C/\ B
		temp = ncsb.copyCSet();
		temp.and(B);
		addLevelRankingState(lvlrk, temp, 2, true);
		// S
		addLevelRankingState(lvlrk, ncsb.getSSet(), 1, false);

		return lvlrk;
	}
	
	private void addLevelRankingState(LevelRankingState<LETTER, STATE> lvlrk, IntSet states, int rank, boolean isInB) {
		IntIterator iterSet = states.iterator();
		while (iterSet.hasNext()) {
			int decker = iterSet.next();
			int downState = mComplementBuchi.getDownState(decker);
			int upState = mComplementBuchi.getUpState(decker);
			lvlrk.addRank(getStackState(downState), mOperandBuchi.getNwaSTATE(upState), rank, isInB);
		}
	}
	

	/**
	 * Return state of result automaton that represents detState. If no such state was constructed yet, construct it.
	 */
	private STATE getOrAdd(final boolean isInitial, int sId) {
		STATE resState = mIdStateMap.get(sId);
		if (resState == null) {
			resState = getRelatedSTATE(sId);
			mIdStateMap.put(sId, resState);
			mStateIdMap.put(resState, sId);
			mSetOfStates.addState(isInitial, mComplementBuchi.isFinal(sId), resState);
		} else {
			assert !isInitial;
		}
		return resState;
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		return mSetOfStates.getInitialStates();
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mOperand.getVpAlphabet();
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mSetOfStates.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return mSetOfStates.isAccepting(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return mSetOfStates.getEmptyStackState();
	}

	@Override
	public int size() {
		return mSetOfStates.getStates().size();
	}


	@Override
	public String sizeInformation() {
		return "State size: " + mSetOfStates.getStates().size();
	}

	@Override
	public Collection<STATE> internalSuccessors(final STATE state, final LETTER letter) {
		// compute the successors on-the-fly
		int letterId = mLetterIdMap.get(letter);
		StateNwaNCSB s = (StateNwaNCSB) mComplementBuchi.getState(mStateIdMap.get(state));
		IntSet succs = s.getSuccessorsInternal(letterId);
		return computeSuccessors(succs);
	}

	@Override
	public Collection<STATE> callSuccessors(final STATE state, final LETTER letter) {
		int letterId = mLetterIdMap.get(letter);
		StateNwaNCSB s = (StateNwaNCSB)mComplementBuchi.getState(mStateIdMap.get(state));
		IntSet succs = s.getSuccessorsCall(letterId);
		return computeSuccessors(succs);
	}
	
	private Collection<STATE> computeSuccessors(IntSet succs) {
		IntIterator iter = succs.iterator();
		final List<STATE> computedSuccs = new ArrayList<>();
		while(iter.hasNext()) {
			STATE succ = getOrAdd(false, iter.next());
			computedSuccs.add(succ);
		}
		return computedSuccs;
	}

	@Override
	public Collection<STATE> returnSuccessorsGivenHier(final STATE state, final STATE hier, final LETTER letter) {
		int letterId = mLetterIdMap.get(letter);
		StateNwaNCSB s = (StateNwaNCSB)mComplementBuchi.getState(mStateIdMap.get(state));
		IntSet succs = s.getSuccessorsReturn(mStateIdMap.get(hier), letterId);
		return computeSuccessors(succs);
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		throw new UnsupportedOperationException();
	}
}
