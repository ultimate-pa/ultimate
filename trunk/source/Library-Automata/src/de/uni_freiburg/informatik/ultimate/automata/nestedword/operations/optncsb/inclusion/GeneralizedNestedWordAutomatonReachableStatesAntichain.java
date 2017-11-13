/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;


/**
 * A nested word automaton with reachable states information.
 *
 * @author Yong Li (liyong@ios.ac.cn)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class GeneralizedNestedWordAutomatonReachableStatesAntichain<LETTER, STATE> extends AbstractGeneralizedAutomatonReachableStates<LETTER, STATE> {
	
	private final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	private final ComplementNwaOutgoingLetterAndTransitionAdapter<LETTER, STATE> mSndOperand;

	private final Map<STATE, ProductStateContainer> mStates = new HashMap<>();
	
	private final Map<STATE, Map<STATE, ProductStateContainer>> mFst2snd2res = new HashMap<>();
	
	private final ReachableStatesComputation mReach;
		
	private final IBuchiIntersectStateFactory<STATE> mStateFactory;
	private final STATE mEmptyStackState;
	private final int mAcceptanceSize;
	private static int mNumber = 0;
	
	public <FACTORY extends IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> GeneralizedNestedWordAutomatonReachableStatesAntichain(final AutomataLibraryServices services,
			final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final ComplementNwaOutgoingLetterAndTransitionAdapter<LETTER, STATE> sndOperand,
			final FACTORY stateFactory) throws AutomataLibraryException {
		super(services, fstOperand.getVpAlphabet());
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		if (!NestedWordAutomataUtils.sameAlphabet(mFstOperand, mSndOperand)) {
			throw new AutomataLibraryException(this.getClass(),
					"Unable to apply operation to automata with different alphabets.");
		}
		mStateFactory = stateFactory;
		mEmptyStackState = mStateFactory.createEmptyStackState();
		mDownStates.add(mEmptyStackState);
		mAcceptanceSize = fstOperand.getAcceptanceSize() + 1;
		try {
			mReach = new ReachableStatesComputation();
//			new RemoveUnusedStates<>(mServices, this);
			mFinalStates.clear();
		} catch (final ToolchainCanceledException tce) {
			throw tce;
		} catch (final Error | RuntimeException e) {
			throw e;
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(stateContainerInformation());
		}
		
//		
//		final boolean dumpFile = true;
//		if(dumpFile) {
//			mNumber ++;
//			GeneralizedBuchiToBuchi<LETTER, STATE> gba2ba = new GeneralizedBuchiToBuchi<>(stateFactory, mFstOperand);
//			new AutomatonDefinitionPrinter<String, String>(mServices, "Program",
//					"./program" + mNumber, Format.BA, "", gba2ba);
//			new AutomatonDefinitionPrinter<String, String>(mServices, "Complement",
//					"./complement" + mNumber, Format.BA, "", mSndOperand);
//			gba2ba = new GeneralizedBuchiToBuchi<>(stateFactory, this);
//			new AutomatonDefinitionPrinter<String, String>(mServices, "Difference",
//					"./difference" + mNumber, Format.BA, "", gba2ba);
//		}
	}
	
	@Override
	protected StateContainer<LETTER, STATE> getStateContainer(STATE state) {
		return mStates.get(state);
	}
	
	private String stateContainerInformation() {
		return mStates.size() + " StateContainers ";
	}
	
	@Override
	public Boolean isEmpty() {
		return mReach.mIsEmpty;
	}
	
	private NestedLassoRun<LETTER, STATE> mLasso = null;
	
	// have to use information in tarjan
	public NestedLassoRun<LETTER, STATE> getNestedLassoRun() throws AutomataOperationCanceledException {
		if(mReach.mIsEmpty) return null;
		// construct lasso run
		if(mLasso == null) {
			for(List<STATE> scc : mReach.mSccList) {
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
	
	private void print(String name, INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) {
		try {
			PrintWriter out = new PrintWriter(new FileWriter("./" + name));
			List<STATE> workList = new ArrayList<>();
			for(STATE state : operand.getInitialStates()) {
				out.println("Initial States: " + mSndOperand.getNCSB(state) + " final: " + mSndOperand.isFinal(state));
				workList.add(state);
			}
			Set<STATE> visited = new HashSet<>();
			Map<LETTER, Integer> alphabet = new HashMap<>();
			int num = 0;
			for(LETTER letter : operand.getAlphabet()) {
				alphabet.put(letter, num);
				num ++;
			}
			while(!workList.isEmpty()) {
				STATE curr = workList.remove(workList.size()-1);
				if(visited.contains(curr)) continue;
				visited.add(curr);
				out.println("State " + mSndOperand.getNCSB(curr) + " final: " + mSndOperand.isFinal(curr));
				Set<STATE> succs = new HashSet<>();
				for(OutgoingInternalTransition<LETTER, STATE> trans: operand.internalSuccessors(curr)) {
					succs.add(trans.getSucc());
					if(!visited.contains(trans.getSucc())) {
						workList.add(trans.getSucc());
					}
				}
				for(STATE succ : succs) {
					out.println("-> " + mSndOperand.getNCSB(succ));
				}
			}
			out.close();			
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	private boolean reachable(STATE source, STATE target, INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) {
		Set<STATE> visited = new HashSet<>();
		List<STATE> workList = new ArrayList<>();
		workList.add(source);
		while(! workList.isEmpty()) {
			STATE curr = workList.remove(workList.size()-1);
			if(target.equals(curr)) return true;
			if(visited.contains(curr)) continue;
			visited.add(curr);
			for(OutgoingInternalTransition<LETTER, STATE> trans: operand.internalSuccessors(curr)) {
				if(!visited.contains(trans.getSucc())) {
					workList.add(trans.getSucc());
				}
			}
		}
		return false;
	}
	
	private GeneralizedNestedWordAutomatonReachableStatesAntichain<LETTER, STATE> getReach() {
		return this;
	}
	
	@Override
	protected void removeStates(STATE state) {
		mStates.remove(state);
		mInitialStates.remove(state);
		mFinalStates.remove(state);
	}
	
	/**
	 * We use Antichain to reduce some states in reachability analysis
	 * */
	class ReachableStatesComputation {
		
		// variables from Ondra's algorithm and Q' is the mStates
        private int mCnt;
        private final Stack<AsccPair<LETTER, STATE>> mSCCs;
        private final Map<STATE, Integer> mDfsNum;
        private final Stack<STATE> mAct;
        private final Set<STATE> mQPrime;
        private List<LinkedList<STATE>> mSccList; 
        private Boolean mIsEmpty = null;
                
        private final Antichain mEmp; // some kind of empty sets
        
		public ReachableStatesComputation() throws AutomataOperationCanceledException {
			mNumberOfConstructedStates = 0;
			// first construct the initial states
			computeInitialStates();
			
			mCnt = 0;
			mDfsNum = new HashMap<>();
			mAct = new Stack<>();
			mSccList = new ArrayList<>();
			mSCCs = new Stack<>();
			mQPrime = new HashSet<>();
			mEmp = new Antichain();
			
			// initialize
			boolean is_nemp = false;
			for(STATE state : getInitialStates()) {
                if(! mDfsNum.containsKey(state)){
                	final boolean result = construct(state);
                	is_nemp = result || is_nemp;
                }
            }
			
			mIsEmpty = !is_nemp;
			Set<STATE> states = new HashSet<>();
			states.addAll(mStates.keySet());
//			System.err.println
//			System.err.println(mEmp);
//			for(STATE st : mStates.keySet()) {
//				if(mQPrime.contains(st)) {
//					if(mEmp.covers(mStates.get(st).mProdState)) {
//                        print("antichain", mSndOperand);
//						RemoveNonLiveStates<LETTER, STATE> remove = new RemoveNonLiveStates<>(mServices, mSndOperand);
//                        print("simplified", remove.getResult());
//                        ProductState pd = mEmp.coveringProductState(mStates.get(st).mProdState);
//                        STATE cover = pd.mSnd;
//                        STATE covered = mStates.get(st).mProdState.mSnd;
//                        System.out.println("St in QPrime: " + mDfsNum.get(st));
//                        System.out.println("Cr in Antichain: " + mDfsNum.get(pd.mRes));
//                        System.out.println("St -> Cr: " + reachable(st, pd.mRes, getReach()));
//                        System.out.println("Cr -> St: " + reachable(pd.mRes, st, getReach()));
//                        
//                        System.err.println(mSndOperand.getNCSB(cover) + "->" + mSndOperand.getNCSB(covered) + ":" + reachable(cover, covered, remove.getResult()));
//                        System.err.println(mSndOperand.getNCSB(covered) + "->" + mSndOperand.getNCSB(cover) + ":" + reachable(covered, cover, remove.getResult()));
////                        Set<STATE> inits = new HashSet<>();
////                        inits.add(mEmp.coveringProductState(mStates.get(st).mProdState).mSnd);
////                        final NestedWordAutomatonFilteredStates<LETTER, STATE> filtered =
////                				new NestedWordAutomatonFilteredStates<>(mServices, mReach, inits, remove.getResult().getFinalStates());
////                		mResult = new NestedWordAutomatonReachableStates<>(mServices, filtered);
//                        try {
//							new ComplementTest<>(mServices, mStateFactory, mSndOperand.getOperand());
//						} catch (AutomataLibraryException e) {
//							// TODO Auto-generated catch block
//							e.printStackTrace();
//						}
//                		new AutomatonDefinitionPrinter<String, String>(mServices, "usedcomplement",
//                				"./usedcomplement", Format.BA, "", mSndOperand);
//    					assert false : "Wrong Coverage: " + mStates.get(st).mProdState.mFst + ", " + mSndOperand.getNCSB(mStates.get(st).mProdState.mSnd)
//    					+ "\n" + mEmp.coveringProductState(mStates.get(st).mProdState).mFst + ", " + mSndOperand.getNCSB(mEmp.coveringProductState(mStates.get(st).mProdState).mSnd);
//					}
//			    }
//			    states.add(st);
//			}
			for(STATE st : states) {
				if(mQPrime.contains(st)) {
					assert !mEmp.covers(mStates.get(st).mProdState) : "Wrong Coverage: " + mStates.get(st).mProdState.mFst + ", " + mSndOperand.getNCSB(mStates.get(st).mProdState.mSnd)
					+ "\n" + mEmp.coveringProductState(mStates.get(st).mProdState).mFst + ", " + mSndOperand.getNCSB(mEmp.coveringProductState(mStates.get(st).mProdState).mSnd);
					continue;
				}
//				System.err.println(mStates.get(st).mProdState.mFst + ", " + mSndOperand.getNCSB(mStates.get(st).mProdState.mSnd));
				if(mEmp.covers(mStates.get(st).mProdState)) {
					// remove states
					StateContainer<LETTER, STATE> cont = mStates.get(st);
		        	Set<STATE> pred = new HashSet<>();
		        	for(IncomingInternalTransition<LETTER, STATE> trans : cont.internalPredecessors()) {
		        		if (! mServices.getProgressAwareTimer().continueProcessing()) {
		    				final RunningTaskInfo rti = constructRunningTaskInfo();
		    				throw new AutomataOperationCanceledException(rti);
		    			}
		        		StateContainer<LETTER, STATE> predCont = mStates.get(trans.getPred());
		        		if(predCont != null) predCont.removeSuccessor(st);
		        		pred.add(trans.getPred());
		        	}
		        	cont.removePredecessors(pred);
				}else {
					assert false : "You should never be here: " + mStates.get(st).mProdState;
				}
				mStates.remove(st);
				mInitialStates.remove(st);
				mFinalStates.remove(st);
			}
			asccClear();
		}
		
		private void asccClear() {
        	mDfsNum.clear();
        	mQPrime.clear();
        	mEmp.clear();
        }

		private void computeInitialStates() {
			for (final STATE fst : mFstOperand.getInitialStates()) {
				for (final STATE snd : mSndOperand.getInitialStates()) {
					final STATE init = getOrConstructState(fst, snd);
					mInitialStates.add(init);
				}
			}
		}

		/**
		 * Use the kind of style by Matthias to get or construct new state
		 * */
		private STATE getOrConstructState(STATE fst, STATE snd) {
			Map<STATE, ProductStateContainer> snd2Res = mFst2snd2res.get(fst);
			if(snd2Res == null) {
				snd2Res = new HashMap<>();
				mFst2snd2res.put(fst, snd2Res);
			}
			ProductStateContainer prodStateCont = snd2Res.get(snd);
			if(prodStateCont == null) {
				final STATE res = mStateFactory.intersectBuchi(fst, snd, 1);
				ProductState prodState = new ProductState(fst, snd, res);
				prodState.setAcceptanceSet(computeAcceptance(fst, snd));
				prodStateCont = new ProductStateContainer(res, prodState); 
				snd2Res.put(snd, prodStateCont);
				mStates.put(res, prodStateCont);
				if(!prodState.mAcceptanceSet.isEmpty()) {
					mFinalStates.add(res);
				}
				mNumberOfConstructedStates ++;
			}
			return prodStateCont.getState();
		}
		
		private Set<Integer> computeAcceptance(STATE fst, STATE snd) {
			final Set<Integer> acc = new HashSet<>();
			Set<Integer> fstAcc = mFstOperand.getAcceptanceLabels(fst);		
			for(Integer index : fstAcc) {
				acc.add(index);
			}
			int fstSize = mFstOperand.getAcceptanceSize();
			if(mSndOperand.isFinal(snd)) acc.add(fstSize);
			
			if(acc.isEmpty()) return Collections.emptySet();
			return acc;
		}
		// here the local variable is_nonempty is useful to identify states which have empty languages
		// empty is Antichain to store empty states (have empty languages)
		// 
		boolean construct(STATE state) throws AutomataOperationCanceledException {
            
			ProductStateContainer prodStateCont = mStates.get(state);
			boolean is_nemp = false;
			mCnt ++;
            mDfsNum.put(state, mCnt);
            mAct.push(state);
            mSCCs.push(new AsccPair<>(state, prodStateCont.mProdState.getAcceptanceSet()));
            
            for(final OutgoingInternalTransition<LETTER, STATE> fstTrans : mFstOperand
            		.internalSuccessors(prodStateCont.mProdState.getFst())) {
            	for(final OutgoingInternalTransition<LETTER, STATE> sndTrans : mSndOperand
            				.internalSuccessors(prodStateCont.mProdState.getSnd(), fstTrans.getLetter())) {
            		if (! getServices().getProgressAwareTimer().continueProcessing()) {
						final RunningTaskInfo rti = constructRunningTaskInfo();
						throw new AutomataOperationCanceledException(rti);
					}
            		STATE succState = getOrConstructState(fstTrans.getSucc(), sndTrans.getSucc());
            		ProductState succProd = mStates.get(succState).getProd();
            		prodStateCont.addInternalOutgoing(new OutgoingInternalTransition<>(fstTrans.getLetter(), succState));
            		mStates.get(succState).addInternalIncoming(new IncomingInternalTransition<>(state, fstTrans.getLetter()));
            		
            		if(mQPrime.contains(succState)) is_nemp = true;
            		else if(mEmp.covers(succProd)) continue;
            		else if(!mAct.contains(succState)) {
                    	final boolean result = construct(succState);
                		is_nemp = result || is_nemp;
            		}else {
            			Set<Integer> B = new HashSet<>();
                        STATE u;
                        do {
                        	AsccPair<LETTER, STATE> pair = mSCCs.pop();
                        	u = pair.mState;
                        	B.addAll(pair.mLabels);
                            if(B.size() == getAcceptanceSize()) {
                                is_nemp = true;
                            }
                        }while(mDfsNum.get(u) > mDfsNum.get(succState));
                        mSCCs.push(new AsccPair<>(u, B));
            		}
            	}
            }
            if(mSCCs.peek().mState.equals(state)){
                AsccPair<LETTER, STATE> pair = mSCCs.pop(); // remove the root
                STATE u;
                LinkedList<STATE> scc = new LinkedList<>();
                do {
                    assert !mAct.isEmpty() : "Active stack is empty";
                    // pop all states in the same SCC
                    u = mAct.pop();
                    scc.add(u);
                    if(is_nemp) {
                    	assert !mEmp.covers(mStates.get(u).mProdState) : "Add wrong states" +
                    		mEmp.toString() + "\n " + mStates.get(u).mProdState.mFst + 
                    		", " + mSndOperand.getNCSB(mStates.get(u).mProdState.mSnd);
                    	mQPrime.add(u);
                    }else {
                    	mEmp.addState(mStates.get(u).mProdState);
                    }
                }while(!u.equals(state)); 
                // whether there is accepting loop
                if(pair.mLabels.size() == getAcceptanceSize()) {
                	if(scc.size() > 1
                	|| prodStateCont.hashSelfloop()) {
                		mSccList.add(scc);
                	}
                }
            }
            return is_nemp;
		}
	}
	
	private class AsccPair<LETTER, STATE> {
		final STATE mState;
		final Set<Integer> mLabels;
		
		AsccPair(STATE state, Set<Integer> labels) {
			this.mState = state;
			this.mLabels = labels;
		}
		
		@Override
		public boolean equals(Object obj) {
			if(this == obj) return true;
			if(!(obj instanceof AsccPair)) {
				return false;
			}
			@SuppressWarnings("unchecked")
			AsccPair<LETTER, STATE> other = (AsccPair<LETTER, STATE>)obj;
			return mState.equals(other.mState)
			   &&  mLabels.equals(other.mLabels);
		}
		
		@Override
		public int hashCode() {
			return mState.hashCode() + mLabels.hashCode();
		}
	}
	
	// -----------------------------------------------------------

	private AutomataLibraryServices getServices() {
		return mServices;
	}


	private RunningTaskInfo constructRunningTaskInfo() {
		final String taskDescription = "computing reachable states (" + mNumberOfConstructedStates
				+ " states constructed" + "input type " + this.getClass().getSimpleName() + ")";
		final RunningTaskInfo rti = new RunningTaskInfo(getClass(), taskDescription);
		return rti;
	}

	
	@Override
	public Set<STATE> getStates() {
		return mStates.keySet();
	}

	@Override
	public Set<STATE> getInitialStates() {
		return Collections.unmodifiableSet(mInitialStates);
	}

	@Override
	public Collection<STATE> getFinalStates() {
		return Collections.unmodifiableSet(mFinalStates);
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
		return size() + " states";
	}

	@Override
	public STATE getEmptyStackState() {
		return mEmptyStackState;
	}

	@Override
	public boolean isInitial(STATE state) {
		return mInitialStates.contains(state);
	}


	@Override
	public int getAcceptanceSize() {
		return mAcceptanceSize;
	}

	@Override
	public boolean isFinal(STATE state, int index) {
		return mStates.get(state).mProdState.mAcceptanceSet.contains(index);
	}

	@Override
	public Set<Integer> getAcceptanceLabels(STATE state) {
		return mStates.get(state).mProdState.mAcceptanceSet;
	}
	

	@Override
	public boolean isFinal(STATE state) {
		return !getAcceptanceLabels(state).isEmpty();
	}

	
	//------------------------------------------------------
	private class ProductStateContainer extends StateContainer<LETTER, STATE> {
		ProductState mProdState;
		public ProductStateContainer(STATE state, ProductState prod) {
			super(state);
			mProdState = prod;
		}
		
		ProductState getProd() {
			return mProdState;
		}
	}
	
	/**
	 * Product state for Generalized Buchi automata.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @author liyong
	 */
	private class ProductState {
		private final STATE mFst;
		private final STATE mSnd;
		private final STATE mRes;
		private Set<Integer> mAcceptanceSet;

		ProductState(final STATE fst, final STATE snd, final STATE res) {
			mFst = fst;
			mSnd = snd;
			mRes = res;
		}

		public STATE getFst() {
			return mFst;
		}

		public STATE getSnd() {
			return mSnd;
		}

		public STATE getRes() {
			return mRes;
		}
		
		public void setAcceptanceSet(Set<Integer> acceptance) {
			mAcceptanceSet = acceptance;
		}
		
		public boolean coveredBy(ProductState other) {
			return mFst.equals(other.mFst)
			   && mSndOperand.coveredBy(mSnd, other.mSnd);
		}
		
		public Set<Integer> getAcceptanceSet() {
			return mAcceptanceSet;
		}

		@Override
		public String toString() {
			return "<" + mFst.toString() + "," + mSnd.toString() + "," + mAcceptanceSet.toString() +  ">";
		}
	}
	
	// ----------------------------------------------------
	private class Antichain {
	    private final Map<STATE, List<ProductState>> mResStateMap;
	    
	    public Antichain() {
	    	mResStateMap = new HashMap<>();
	    }
	    
	    void clear() {
	    	mResStateMap.clear();
	    }
	    
	    Set<STATE> getStates() {
	    	return mResStateMap.keySet();
	    }
	    
	    public boolean addState(ProductState state) {
	        
	        final STATE fstState = state.getFst();
	        List<ProductState> sndElem = mResStateMap.get(fstState);
	        
	        if(sndElem == null) {
	            sndElem = new ArrayList<>();
	        }
	        List<ProductState> copy = new ArrayList<>();
	        //avoid to add pairs are covered by other pairs
	        for(int i = 0; i < sndElem.size(); i ++) {
	            ProductState elem = sndElem.get(i);
	            //pairs covered by the new pair
	            //will not be kept in copy
	            if(elem.coveredBy(state)) {
	                continue;
	            }else if(state.coveredBy(elem)) {
	                return false;
	            }
	            copy.add(elem);
	        }
	        
	        copy.add(state); // should add snd
	        mResStateMap.put(fstState, copy);
	        return true;
	    }
	    
	    public boolean covers(ProductState state) {
	        List<ProductState> sndElem = mResStateMap.get(state.getFst());
	        if(sndElem == null) return false;
	        for(int i = 0; i < sndElem.size(); i ++) {
	        	ProductState elem = sndElem.get(i);
	            if(state.coveredBy(elem)) { // no need to add it
	                return true;
	            }
	        }
	        return false;
	    }
	    
	    public ProductState coveringProductState(ProductState state) {
	    	List<ProductState> sndElem = mResStateMap.get(state.getFst());
	        if(sndElem == null) return null;
	        for(int i = 0; i < sndElem.size(); i ++) {
	        	ProductState elem = sndElem.get(i);
	            if(state.coveredBy(elem)) { // no need to add it
	                return elem;
	            }
	        }
	        return null;
	    }
	    
	    public String toString() {
	        StringBuilder sb = new StringBuilder();
	        for(Entry<STATE, List<ProductState>> entry : mResStateMap.entrySet()) {
	            sb.append(entry.getKey() + " -> " + entry.getValue() + "\n");
	        }
	        return sb.toString();
	    }
	}


}
