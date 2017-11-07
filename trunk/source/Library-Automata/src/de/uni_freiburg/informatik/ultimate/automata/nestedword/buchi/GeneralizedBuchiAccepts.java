/*
 * Copyright (C) 2017      Yong Li  (liyong@ios.ac.cn)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import gnu.trove.map.TObjectIntMap;
import gnu.trove.map.hash.TObjectIntHashMap;

/**
 * Class that provides the Generalized Buchi acceptance check.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Yong Li 
 * @param <LETTER>
 *            Symbol. Type of the symbols used as alphabet.
 * @param <STATE>
 *            Content. Type of the labels ("the content") of the automata states.
 */
public final class GeneralizedBuchiAccepts<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>>{
	/**
	 * Stem of the nested lasso word whose acceptance is checked.
	 */
	private final NestedWord<LETTER> mStem;

	/**
	 * Loop of the nested lasso word whose acceptance is checked.
	 */
	private final NestedWord<LETTER> mLoop;
	
	private final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	
	private final Boolean mIsAccepted;

	/**
	 * Check if a Buchi nested word automaton accepts a nested lasso word.
	 * <p>
	 * Returns true iff nlw is accepted by nwa. Note that here a nested lasso word is always rejected if its loop
	 * contains pending returns.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param nlw
	 *            NestedLassoWord whose acceptance is checked
	 * @param operand
	 *            NestedWordAutomaton which is interpreted as Buchi nested word automaton here
	 * @throws AutomataLibraryException
	 *             if accept fails
	 */
	public GeneralizedBuchiAccepts(final AutomataLibraryServices services, final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final NestedLassoWord<LETTER> nlw) throws AutomataLibraryException {
		super(services);
		mOperand = operand;
		mStem = nlw.getStem();
		mLoop = nlw.getLoop();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		// actually not necessary
		if (mStem.containsPendingReturns()) {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("This implementation of Buchi acceptance rejects lasso words, where the stem contains "
						+ "pending returns.");
			}
			mIsAccepted = false;
			return;
		}

		if (mLoop.containsPendingReturns()) {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("This implementation of Buchi acceptance rejects lasso words, where the loop contains "
						+ "pending returns.");
			}
			mIsAccepted = false;
			return;
		}

		if (mLoop.length() == 0) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("LassoWords with empty lasso are rejected by every Büchi automaton");
			}
			mIsAccepted = false;
			return;
		}

		mIsAccepted = buchiAccepts();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName() + " Operand " + mOperand.sizeInformation() + " Stem has " + mStem.length()
				+ " letters." + " Loop has " + mLoop.length() + " letters.";
	}

	private boolean buchiAccepts() throws AutomataLibraryException {
		Ascc ascc = new Ascc(); 
		return ! ascc.mIsEmpty;
	}

	@Override
	public Boolean getResult() {
		return mIsAccepted;
	}

	@Override
	protected IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}
	
	private class StackElement<LETTER, STATE> {
		final STATE mState;
		final int mIndex;
		
		StackElement(STATE state, int index) {
			mState = state;
			mIndex = index;
		}
		
		@Override
		public String toString() {
			return "[" + mState + ", " + mIndex + "]"; 
		}
		
		@Override
		public boolean equals(Object obj) {
			if(this == obj) return true;
			if(! (obj instanceof StackElement)) {
				return false;
			}
			@SuppressWarnings("unchecked")
			StackElement<LETTER, STATE> other = (StackElement<LETTER, STATE>)obj;
			return mState.equals(other.mState)
				&& mIndex == other.mIndex;
		}
		
		private boolean hasCode = false;
		int hashCode ;
		
		@Override
		public int hashCode() {
			if(hasCode) return hashCode;
			hasCode = true;
			hashCode = 1;
			hashCode = hashCode * 31 + mState.hashCode();
			hashCode = hashCode * 31 + mIndex;
			return hashCode;
		}
	}
	
	// -------- use following like we have an automaton
	// 0->st[1]->1->...->st[m]->m -> lp[1] -> m+1 -> ... -> lp[n] -> m+n -> lp[1] -> m+1
	private int getNextState(int index) {
		if(index < mStem.length() + mLoop.length()) {
			return index + 1;
		}
		assert index == mStem.length() + mLoop.length();
		return mStem.length() + 1;
	}
	
	private LETTER getNextLetter(int state) {
		assert state <= mStem.length() + mLoop.length();
		if(state < mStem.length()) {
			return mStem.getSymbol(state);
		}
		if(state < mStem.length() + mLoop.length()) {
			return mLoop.getSymbol(state - mStem.length());
		}
		assert state == mStem.length() + mLoop.length();
		return mLoop.getSymbol(0);
	}
	
	private boolean isFinalState(int state) {
		return state > mStem.length();
	}
	
	private class AsccPair {
		StackElement<LETTER, STATE> mElem;
		Set<Integer> mLabels;
		AsccPair(StackElement<LETTER, STATE> elem, Set<Integer> labels) {
			mElem = elem;
			mLabels = labels;
		}
	}
	
	private Set<Integer> getAcceptanceLabels(StackElement<LETTER, STATE> prod) {
		Set<Integer> labels = new HashSet<>();
		labels.addAll(mOperand.getAcceptanceLabels(prod.mState));
		if(isFinalState(prod.mIndex)) {
			labels.add(mOperand.getAcceptanceSize());
		}
		return labels;
	}
	
    private class Ascc {
        
        private int mDepth;
        private final Stack<AsccPair> mRootsStack;             // C99 's root stack
        private final Stack<StackElement<LETTER, STATE>> mActiveStack;            // tarjan's stack
        private final TObjectIntMap<StackElement<LETTER, STATE>> mDfsNum;
        private final Set<StackElement<LETTER, STATE>> mCurrent;
        
        private Boolean mIsEmpty = null;
                
        public Ascc() throws AutomataOperationCanceledException {
            
            this.mRootsStack = new Stack<>();
            this.mActiveStack = new Stack<>();
            this.mDfsNum = new TObjectIntHashMap<>();
            this.mCurrent = new HashSet<>();
            
            for(STATE state : mOperand.getInitialStates()) {
            	StackElement<LETTER, STATE> prod = new StackElement<>(state, 0);
                if(! mDfsNum.containsKey(prod)){
                    strongConnect(prod);
                }
            }
            
            if(mIsEmpty == null) {
                mIsEmpty = true;
            }
        }
        
        void strongConnect(StackElement<LETTER, STATE> prod) throws AutomataOperationCanceledException {
            
            ++ mDepth;
            mDfsNum.put(prod, mDepth);
            mRootsStack.push(new AsccPair(prod, getAcceptanceLabels(prod)));
            mActiveStack.push(prod);
            mCurrent.add(prod);
            
            for(OutgoingInternalTransition<LETTER, STATE> trans 
            		: mOperand.internalSuccessors(prod.mState, getNextLetter(prod.mIndex))) {
    			if (mServices.getProgressAwareTimer() != null && !mServices.getProgressAwareTimer().continueProcessing()) {
    				throw new AutomataOperationCanceledException(this.getClass());
    			}
            	StackElement<LETTER, STATE> prodSucc = 
            			new StackElement<LETTER, STATE>(trans.getSucc(), getNextState(prod.mIndex));
            	if(! mDfsNum.containsKey(prodSucc)) {
                    strongConnect(prodSucc);
                }else if(mCurrent.contains(prodSucc)) {
                    // we have already seen it before, there is a loop
                    Set<Integer> labels = new HashSet<>();
                    while(true) {
                        //pop element u
                    	AsccPair pair = mRootsStack.pop();
                    	StackElement<LETTER, STATE> stackTop = pair.mElem;
                    	labels.addAll(pair.mLabels);
                        // found one accepting scc
                        if(labels.size() == mOperand.getAcceptanceSize() + 1) {
                            mIsEmpty = false;
                        }
                        if(mDfsNum.get(stackTop) <= mDfsNum.get(prodSucc)) {
                            mRootsStack.push(new AsccPair(stackTop, labels)); // push back
                            break;
                        }
                    }
                }
            }
            
            // if current state is done, 
            // then we should remove all 
            // active states in the same scc
            if(mRootsStack.peek().mElem.equals(prod)) {
                mRootsStack.pop();
                while(true) {
                    StackElement<LETTER, STATE> stackTop = mActiveStack.pop(); // Tarjan' Stack
                    mCurrent.remove(stackTop);
                    if(stackTop.equals(prod)) break;
                }
            }
        }
        
    }

}
