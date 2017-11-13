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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiToGeneralizedBuchi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.Options;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import gnu.trove.map.TObjectIntMap;
import gnu.trove.map.hash.TObjectIntHashMap;

public class GetLassoRunFromLassoWord<LETTER, STATE> extends AbstractGeneralizedAutomatonReachableStates<LETTER, STATE> {
	
	private final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	
	protected final IStateFactory<STATE> mStateFactory;

	private final Map<STATE, StateContainer<LETTER, STATE>> mStates = new HashMap<>();
	
	private final ReachableStatesComputationTarjan mReach;
	
	private final NestedWord<LETTER> mStem;
	private final NestedWord<LETTER> mLoop;
	
	@SuppressWarnings("unchecked")
	public GetLassoRunFromLassoWord(AutomataLibraryServices services,
			INestedWordAutomaton<LETTER, STATE> operand, NestedLassoWord<LETTER> lassoWord)  throws AutomataOperationCanceledException {
		super(services, operand.getVpAlphabet());
		mStateFactory = operand.getStateFactory();
		mDownStates.add(operand.getEmptyStackState());
		if(operand instanceof IGeneralizedNwaOutgoingLetterAndTransitionProvider) {
			mOperand = (IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE>)operand;
//			IBuchiIntersectStateFactory<STATE> sf = (IBuchiIntersectStateFactory<STATE>)operand.getStateFactory();
//			GeneralizedBuchiToBuchi<LETTER, STATE> buchi = new GeneralizedBuchiToBuchi<>(sf, mOperand);
//			BuchiAccepts<LETTER, STATE> checker;
//			try {
//				checker = new BuchiAccepts<>(services,buchi, lassoWord);
//				System.err.println("Accepts: " + checker.getResult());
//			} catch (AutomataLibraryException e) {
//				// TODO Auto-generated catch block
//				e.printStackTrace();
//			}
		}else {
			mOperand = new BuchiToGeneralizedBuchi<LETTER, STATE>(operand);
//			try {
//				BuchiAccepts<LETTER, STATE> checker = new BuchiAccepts<>(services, operand, lassoWord);
//				System.err.println("Accepts: " + checker.getResult());
//			} catch (AutomataLibraryException e) {
//				// TODO Auto-generated catch block
//				e.printStackTrace();
//			}
		}
		mStem = lassoWord.getStem();
		mLoop = lassoWord.getLoop();
		if(!mOperand.getVpAlphabet().getCallAlphabet().isEmpty()
		|| !mOperand.getVpAlphabet().getReturnAlphabet().isEmpty()) {
			throw new UnsupportedOperationException("Calls or Returns are not empty");
		}
		if(mLoop.length() == 0) {
			throw new UnsupportedOperationException("Loop is empty");
		}
		try {
			mReach = new ReachableStatesComputationTarjan();
		} catch (final ToolchainCanceledException tce) {
			throw tce;
		} catch (final Error | RuntimeException e) {
			throw e;
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(stateContainerInformation());
		}
	}
	
	// -------- use following like we have an automaton
	// 0->st[1]->1->...->st[m]->m -> lp[1] -> m+1 -> ... -> lp[n] -> m+n -> lp[1] -> m+1
	protected int getNextState(int index) {
		if(index < mStem.length() + mLoop.length()) {
			return index + 1;
		}
		assert index == mStem.length() + mLoop.length();
		return mStem.length() + 1;
	}
	
	protected LETTER getNextLetter(int state) {
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
	
	@Override
	protected StateContainer<LETTER, STATE> getStateContainer(STATE state) {
		return mStates.get(state);
	}
	
	private String stateContainerInformation() {
		return mStates.size() + " StateContainers ";
	}
	
	private StateContainer<LETTER, STATE> getOrAddState(STATE state) {
		StateContainer<LETTER, STATE> cont = mStates.get(state);
		if(cont == null) {
			cont = new StateContainer<>(state);
			mStates.put(state, cont);
		}
		return cont;
	}
	
	@Override
	public Boolean isEmpty() {
		return mReach.isEmpty();
	}
		
	// have to use information in tarjan
	@Override
	public NestedLassoRun<LETTER, STATE> getNestedLassoRun() throws AutomataOperationCanceledException {
		if(mReach.isEmpty()) return null;
		// construct lasso run
		if(mLasso == null) {
			for(List<STATE> scc : mReach.getLoopList()) {
				LassoConstructor<LETTER, STATE> lc = new LassoConstructor<>(mServices, this, scc);
				NestedLassoRun<LETTER, STATE> lasso = lc.getNestedLassoRun();
				if(mLasso == null
				|| (mLasso.getStem().getLength() + mLasso.getLoop().getLength()
						> lasso.getStem().getLength() + lasso.getLoop().getLength())) {
					mLasso = lasso;
				}
			}
		}
		return mLasso;
	}
	
	class ReachableStatesComputationTarjan {
		private Tarjan mTarjan ;
		
		public ReachableStatesComputationTarjan() throws AutomataOperationCanceledException {
			mNumberOfConstructedStates = 0;
			mTarjan = new Tarjan();
		}
		
		public Boolean isEmpty() {
			return mTarjan.mIsEmpty;
		}
		
		public List<List<STATE>> getLoopList() {
			return mTarjan.mSCC;
		}

	    private class Tarjan {
	        
	        private int mIndex;
	        private final Stack<STATE> mStack;             // tarjan's stack
	    	private final TObjectIntMap<STATE> mIndexMap ;
	    	private final TObjectIntMap<STATE> mLowlinkMap;
	        private List<List<STATE>> mSCC;
	        private Boolean mIsEmpty = null;
	                
	        public Tarjan() throws AutomataOperationCanceledException {
	            
	            this.mStack = new Stack<>();
	            this.mIndexMap = new TObjectIntHashMap<>();
	            this.mLowlinkMap = new TObjectIntHashMap<>();
	            this.mSCC = new ArrayList<>();
	            this.mIndex = 0;
	            for(STATE state : mOperand.getInitialStates()) {
	            	mInitialStates.add(state);
	                if(! mIndexMap.containsKey(state)){
	                    strongConnect(state, 0);
	                }
	            }
	            
	            if(mIsEmpty == null) {
	                mIsEmpty = true;
	            }
	        }
	        
	        void strongConnect(STATE state, int wordState) throws AutomataOperationCanceledException {
	            
	    		mStack.push(state);
	    		mIndexMap.put(state, mIndex);
	    		mLowlinkMap.put(state, mIndex);
	    		
	    		++ mIndex;	
	            ++ mNumberOfConstructedStates;
	            
	            StateContainer<LETTER, STATE> cont = getOrAddState(state);
	            for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(state, getNextLetter(wordState))) {
					if (! getServices().getProgressAwareTimer().continueProcessing()) {
						final RunningTaskInfo rti = constructRunningTaskInfo();
						throw new AutomataOperationCanceledException(rti);
					}
					STATE succ = trans.getSucc();
					if(! mIndexMap.containsKey(succ)) {
						strongConnect(succ, getNextState(wordState)); // did not visit succ before
	                    mLowlinkMap.put(state, Math.min(mLowlinkMap.get(state), mLowlinkMap.get(succ)));					
					}else if(mStack.contains(succ)) {
					    mLowlinkMap.put(state, Math.min(mLowlinkMap.get(state), mIndexMap.get(succ)));					
					}
					// explore new states, then we should add state information
					cont.addInternalOutgoing(trans);
					StateContainer<LETTER, STATE> succSc = getOrAddState(succ);
					succSc.addInternalIncoming(new IncomingInternalTransition<>(state, trans.getLetter()));
                }

	    		// found one strongly connected component
	    		if(mLowlinkMap.get(state) == mIndexMap.get(state)){
	    			
	    			Set<Integer> labels = new HashSet<>();
	    			List<STATE> sccList = new ArrayList<>();
	    			
	    			while(! mStack.empty()){
	    				STATE stackTop = mStack.pop();
	    				labels.addAll(mOperand.getAcceptanceLabels(stackTop));
	    				sccList.add(stackTop);
	    				if(stackTop.equals(state))
	    					break;
	    			}

	    			boolean hasAcc = mOperand.getAcceptanceSize() == labels.size();	    			
	    			if(sccList.size() == 1 // only has a single state
	    					&& hasAcc            // it is an accepting states
	    					) {
	    				// if there is no self loop
	    				if(! cont.hashSelfloop()) hasAcc = false;
	    			}
	    							
	    			if(hasAcc) {
	    				mIsEmpty = false;
	    				mSCC.add(sccList);
	    				if(Options.verbose) {
	    					System.out.println("Loop: " + sccList);
	    				}
	    			}
	    		}
	        }
	    }
	}


	private AutomataLibraryServices getServices() {
		return mServices;
	}
	
	private RunningTaskInfo constructRunningTaskInfo() {
		final String taskDescription = "computing reachable states (" + mNumberOfConstructedStates
				+ " states constructed" + "input type " + mOperand.getClass().getSimpleName() + ")";
		final RunningTaskInfo rti = new RunningTaskInfo(getClass(), taskDescription);
		return rti;
	}

	@Override
	public Set<STATE> getStates() {
		return mStates.keySet();
	}

	@Override
	public Set<LETTER> lettersInternalIncoming(STATE state) {
		return mStates.get(state).lettersInternalIncoming();
	}


	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(STATE succ, LETTER letter) {
		return mStates.get(succ).internalPredecessors(letter);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(STATE succ) {
		return mStates.get(succ).internalPredecessors();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(STATE state, LETTER letter) {
		return mStates.get(state).internalSuccessors(letter);
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public int size() {
		return mStates.size();
	}

	@Override
	public String sizeInformation() {
		return null;
	}

	@Override
	public STATE getEmptyStackState() {
		return mOperand.getEmptyStackState();
	}

	@Override
	public boolean isInitial(STATE state) {
		return mOperand.isInitial(state);
	}


	@Override
	public int getAcceptanceSize() {
		return mOperand.getAcceptanceSize();
	}

	@Override
	public boolean isFinal(STATE state, int index) {
		return mOperand.isFinal(state, index);
	}

	@Override
	public Set<Integer> getAcceptanceLabels(STATE state) {
		return mOperand.getAcceptanceLabels(state);
	}
	

	@Override
	public boolean isFinal(STATE state) {
		return !getAcceptanceLabels(state).isEmpty();
	}

}
