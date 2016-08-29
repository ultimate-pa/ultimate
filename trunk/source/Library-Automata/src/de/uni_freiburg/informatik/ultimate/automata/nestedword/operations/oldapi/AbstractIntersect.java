/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public abstract class AbstractIntersect<LETTER, STATE> extends DoubleDeckerBuilder<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
		
	private final INestedWordAutomatonSimple<LETTER, STATE> mFstNwa;
	private final INestedWordAutomatonSimple<LETTER, STATE> mSndNwa;
	private final NestedWordAutomaton<LETTER, STATE> mResultNwa;
	private final IStateFactory<STATE> mContentFactory;
	
	private final boolean mBuchi;
	
	private final Map<STATE, STATE> mResult2fst =
			new HashMap<STATE, STATE>();
	private final Map<STATE, STATE> mResult2snd =
			new HashMap<STATE, STATE>();
	private final Map<STATE, Integer> mResult2track =
			new HashMap<STATE, Integer>();
			
	private final Map<STATE, Map<STATE, STATE>> mTrack1_fst2snd2result = new HashMap<>();
	private final Map<STATE, Map<STATE, STATE>> mTrack2_fst2snd2result = new HashMap<>();
			
	public AbstractIntersect(final AutomataLibraryServices services,
			final boolean buchiIntersection, final boolean minimizeResult,
			final INestedWordAutomatonSimple<LETTER, STATE> fstNwa,
			final INestedWordAutomatonSimple<LETTER, STATE> sndNwa)
					throws AutomataLibraryException {
		super(services);
		
		mBuchi = buchiIntersection;
		mRemoveDeadEnds = minimizeResult;
		mFstNwa = fstNwa;
		mSndNwa = sndNwa;
		if (!NestedWordAutomaton.sameAlphabet(mFstNwa, mSndNwa)) {
			throw new AutomataLibraryException(this.getClass(),
					"Unable to apply operation to automata with different alphabets.");
		}
		
		mContentFactory = mFstNwa.getStateFactory();
		mLogger.info(startMessage());
		
		final Set<LETTER> newInternals = new HashSet<LETTER>();
		newInternals.addAll(mFstNwa.getInternalAlphabet());
		newInternals.retainAll(mSndNwa.getInternalAlphabet());
		final Set<LETTER> newCalls = new HashSet<LETTER>();
		newCalls.addAll(mFstNwa.getCallAlphabet());
		newCalls.retainAll(mSndNwa.getCallAlphabet());
		final Set<LETTER> newReturns = new HashSet<LETTER>();
		newReturns.addAll(mFstNwa.getReturnAlphabet());
		newReturns.retainAll(mSndNwa.getReturnAlphabet());
		
		mResultNwa = new NestedWordAutomaton<LETTER, STATE>(mServices,
				newInternals, newCalls, newReturns, mContentFactory);
		super.mTraversedNwa = mResultNwa;
		super.traverseDoubleDeckerGraph();
		mLogger.info(exitMessage());
		
		if (mBuchi) {
			assert (ResultChecker.buchiIntersect(mServices, mFstNwa, mSndNwa, mResultNwa));
		}
	}
	
	@Override
	public abstract String operationName();
	
	@Override
	public String startMessage() {
		if (mBuchi) {
			return "Start buchiIntersect. First operand " + mFstNwa.sizeInformation() + ". Second operand "
					+ mSndNwa.sizeInformation();
		} else {
			return "Start intersect. First operand " + mFstNwa.sizeInformation() + ". Second operand "
					+ mSndNwa.sizeInformation();
		}
	}
	
	@Override
	public String exitMessage() {
		if (mBuchi) {
			return "Finished buchiIntersect. Result " + mTraversedNwa.sizeInformation();
		} else {
			return "Finished intersect. Result " + mTraversedNwa.sizeInformation();
		}
	}
	
	private STATE getOrConstructOnTrack1(
			final STATE fst, final STATE snd, final boolean isInitial) {
		Map<STATE, STATE> snd2result = mTrack1_fst2snd2result.get(fst);
		if (snd2result == null) {
			snd2result = new HashMap<STATE, STATE>();
			mTrack1_fst2snd2result.put(fst, snd2result);
		}
		STATE state = snd2result.get(snd);
		if (state == null) {
			boolean isFinal;
			if (mBuchi) {
				isFinal = mFstNwa.isFinal(fst);
			} else {
				isFinal = mFstNwa.isFinal(fst) && mSndNwa.isFinal(snd);
			}
			
			if (mBuchi) {
				state = mContentFactory.intersectBuchi(
						fst, snd, 1);
			} else {
				state = mContentFactory.intersection(fst, snd);
			}
			
			mResultNwa.addState(isInitial, isFinal, state);
			snd2result.put(snd, state);
			mResult2fst.put(state, fst);
			mResult2snd.put(state, snd);
			mResult2track.put(state, 1);
		}
		return state;
	}
	
	private STATE getOrConstructOnTrack2(
			final STATE fst, final STATE snd) {
		Map<STATE, STATE> snd2result = mTrack2_fst2snd2result.get(fst);
		if (snd2result == null) {
			snd2result = new HashMap<STATE, STATE>();
			mTrack2_fst2snd2result.put(fst, snd2result);
		}
		STATE state = snd2result.get(snd);
		if (state == null) {
			final boolean isInitial = false;
			final boolean isFinal = false;
			assert mBuchi;
			state = mContentFactory.intersectBuchi(fst, snd, 2);
			mResultNwa.addState(isInitial, isFinal, state);
			snd2result.put(snd, state);
			mResult2fst.put(state, fst);
			mResult2snd.put(state, snd);
			mResult2track.put(state, 2);
		}
		return state;
	}
	
	private int getSuccTrack(final int stateTrack, final STATE fstState, final STATE sndState) {
		int succTrack;
		if (mBuchi) {
			if (stateTrack == 1) {
				if (mFstNwa.isFinal(fstState)) {
					succTrack = 2;
				} else {
					succTrack = 1;
				}
			} else {
				assert (stateTrack == 2);
				if (mSndNwa.isFinal(sndState)) {
					succTrack = 1;
				} else {
					succTrack = 2;
				}
			}
		} else {
			succTrack = 1;
		}
		return succTrack;
	}
	
	@Override
	protected Collection<STATE> getInitialStates() {
//		final int amount = mFstNwa.getInitialStates().size() *
//										mSndNwa.getInitialStates().size();
//		final Collection<STATE> resInits = new ArrayList<STATE>(amount);
		final Collection<STATE> resInits = new ArrayList<STATE>();
		for (final STATE fstInit : mFstNwa.getInitialStates()) {
			for (final STATE sndInit : mSndNwa.getInitialStates()) {
				final STATE resInit = getOrConstructOnTrack1(fstInit, sndInit, true);
				resInits.add(resInit);
			}
		}
		return resInits;
	}
	
	@Override
	protected Collection<STATE> buildInternalSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final STATE resState = doubleDecker.getUp();
		final STATE fstState = mResult2fst.get(resState);
		final STATE sndState = mResult2snd.get(resState);
		final int stateTrack = mResult2track.get(resState);
		final int succTrack = getSuccTrack(stateTrack, fstState, sndState);
		final Collection<STATE> resSuccs = new ArrayList<STATE>();
		for (final LETTER symbol : mFstNwa.lettersInternal(fstState)) {
			for (final OutgoingInternalTransition<LETTER, STATE> fstTrans : mFstNwa.internalSuccessors(fstState,
					symbol)) {
				for (final OutgoingInternalTransition<LETTER, STATE> sndTrans : mSndNwa.internalSuccessors(sndState,
						symbol)) {
					STATE resSucc;
					if (succTrack == 1) {
						resSucc = getOrConstructOnTrack1(fstTrans.getSucc(), sndTrans.getSucc(), false);
					} else {
						assert (succTrack == 2);
						resSucc = getOrConstructOnTrack2(fstTrans.getSucc(), sndTrans.getSucc());
					}
					mResultNwa.addInternalTransition(resState, symbol, resSucc);
					resSuccs.add(resSucc);
				}
			}
		}
		return resSuccs;
	}
	
	@Override
	protected Collection<STATE> buildCallSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final STATE resState = doubleDecker.getUp();
		final STATE fstState = mResult2fst.get(resState);
		final STATE sndState = mResult2snd.get(resState);
		final int stateTrack = mResult2track.get(resState);
		final int succTrack = getSuccTrack(stateTrack, fstState, sndState);
		final Collection<STATE> resSuccs = new ArrayList<STATE>();
		for (final LETTER symbol : mFstNwa.lettersCall(fstState)) {
			for (final OutgoingCallTransition<LETTER, STATE> fstTrans : mFstNwa.callSuccessors(fstState, symbol)) {
				for (final OutgoingCallTransition<LETTER, STATE> sndTrans : mSndNwa.callSuccessors(sndState, symbol)) {
					STATE resSucc;
					if (succTrack == 1) {
						resSucc = getOrConstructOnTrack1(fstTrans.getSucc(), sndTrans.getSucc(), false);
					} else {
						assert (succTrack == 2);
						resSucc = getOrConstructOnTrack2(fstTrans.getSucc(), sndTrans.getSucc());
					}
					mResultNwa.addCallTransition(resState, symbol, resSucc);
					resSuccs.add(resSucc);
				}
			}
		}
		return resSuccs;
	}
	
	@Override
	protected Collection<STATE> buildReturnSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final Collection<STATE> resSuccs = new ArrayList<STATE>();
		final STATE resHierPre = doubleDecker.getDown();
		if (resHierPre == mResultNwa.getEmptyStackState()) {
			return resSuccs;
		}
		final STATE fstHierPre = mResult2fst.get(resHierPre);
		final STATE sndHierPre = mResult2snd.get(resHierPre);
		final STATE resState = doubleDecker.getUp();
		final STATE fstState = mResult2fst.get(resState);
		final STATE sndState = mResult2snd.get(resState);
		final int stateTrack = mResult2track.get(resState);
		final int succTrack = getSuccTrack(stateTrack, fstState, sndState);
		
		for (final LETTER symbol : mFstNwa.lettersReturn(fstState)) {
			for (final OutgoingReturnTransition<LETTER, STATE> fstTrans : mFstNwa.returnSuccessors(fstState, fstHierPre,
					symbol)) {
				for (final OutgoingReturnTransition<LETTER, STATE> sndTrans : mSndNwa.returnSuccessors(sndState,
						sndHierPre, symbol)) {
					STATE resSucc;
					if (succTrack == 1) {
						resSucc = getOrConstructOnTrack1(fstTrans.getSucc(), sndTrans.getSucc(), false);
					} else {
						assert (succTrack == 2);
						resSucc = getOrConstructOnTrack2(fstTrans.getSucc(), sndTrans.getSucc());
					}
					mResultNwa.addReturnTransition(resState, resHierPre, symbol, resSucc);
					resSuccs.add(resSucc);
				}
			}
		}
		return resSuccs;
	}
}
