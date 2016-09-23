/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * Copyright (C) 2010-2015 wuxio
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

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Class that provides the Buchi emptiness check for nested word automata.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author wuxio
 * @version 2010-12-18
 * @param <LETTER>
 *            Symbol. Type of the symbols used as alphabet.
 * @param <STATE>
 *            Content. Type of the labels (the content) of the automata states.
 */
public final class BuchiIsEmptyXW<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE> {
	private static final String LOG_SEPARATOR = "########################################";
	
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final Boolean mResult;
	
	private final Bridge mReachabilityBridge = new Bridge();
	private final Bridge mReachabilityBridgeA = new Bridge();
	private final Bridge mReachabilityBridgeC = new Bridge();
	private final Bridge mReachabilityBridgeAc = new Bridge();
	// TODO: xw: naming
	private STATE mWitnessInitial;
	private STATE mWitnessCritical;
	
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public BuchiIsEmptyXW(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		mResult = checkEmptiness();
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}
	
	@Override
	public String operationName() {
		return "BuchiIsEmptyXW";
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Result is " + mResult;
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}
	
	@Override
	public Boolean getResult() {
		return mResult;
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}
	
	/**
	 * @return An accepting nested lasso run.
	 */
	public NestedLassoRun<LETTER, STATE> getAcceptingNestedLassoRun() {
		if (mResult) {
			if (mLogger.isInfoEnabled()) {
				mLogger.info("There is no accepting nested lasso run");
			}
			return null;
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Starting construction of run");
		}
		final NestedRun<LETTER, STATE> stem = reconstructionC(mWitnessInitial, mWitnessCritical);
		final NestedRun<LETTER, STATE> loop = reconstructionAc(mWitnessCritical, mWitnessCritical);
		final NestedLassoRun<LETTER, STATE> acceptingNestedLassoRun = new NestedLassoRun<>(stem, loop);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Accepting run: " + acceptingNestedLassoRun);
			mLogger.debug("Accepted word:  Stem:" + acceptingNestedLassoRun.getStem().getWord() + " Loop: "
					+ acceptingNestedLassoRun.getLoop().getWord());
		}
		return acceptingNestedLassoRun;
	}
	
	/**
	 * Check if a Buchi nested word automaton accepts any nested lasso word.
	 * 
	 * @return true iff nwa does not accept any nested lasso word.
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	// Requires collections of transitions to be final.
	public boolean checkEmptiness() throws AutomataOperationCanceledException {
		final Worklist worklist = new Worklist();
		final Set<STATE> allStates = new HashSet<>();
		final Set<STATE> acceptingStates = new HashSet<>();
		final Set<STATE> initialStates = new HashSet<>();
		final Collection<LETTER> callAlphabet = mOperand.getCallAlphabet();
		final Collection<LETTER> returnAlphabet = mOperand.getReturnAlphabet();
		
		// Get all states and accepting states
		// TODO: xw: check the consequence of casting
		for (final STATE state : mOperand.getStates()) {
			allStates.add(state);
			if (mOperand.isFinal(state)) {
				acceptingStates.add(state);
			}
		}
		
		// Get all initial states
		// TODO: xw: check the consequence of casting
		for (final STATE state : mOperand.getInitialStates()) {
			initialStates.add(state);
		}
		
		// Reachability
		// Bridge reachabilityBridge = new Bridge();
		
		// line2--5
		// TODO: xw: naming?
		for (final STATE q : allStates) {
			for (final STATE p : getCallPredStates(q, callAlphabet)) {
				for (final STATE pprime : getReturnSuccStates(q, p, returnAlphabet)) {
					addReachabilityBridgeIfNotPresent(worklist, q, p, pprime);
				}
			}
		}
		// line6--8
		addReachabilityBridgeInternalPredecessors(worklist, allStates);
		
		// line9
		while (!worklist.isEmpty()) {
			final StatePair workPair = worklist.dequeue();
			// line11--13
			extendPathCallReturn(workPair.mSource, workPair.mTarget, callAlphabet, returnAlphabet, mReachabilityBridge,
					worklist);
			// line14-16
			extendPathBeyondDestination(workPair.mSource, workPair.mTarget, mReachabilityBridge, worklist);
			// line17-19
			extendPathBeyondOrigin(workPair.mSource, workPair.mTarget, mReachabilityBridge, worklist);
			
			if (isCancellationRequested()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		
		// Reachability-A
		// Bridge reachabilityBridgeA = new Bridge();
		
		assert worklist.isEmpty();
		for (final STATE acceptingState : acceptingStates) {
			// line3--9
			extendAcceptingPath(acceptingState, mReachabilityBridge, mReachabilityBridgeA, worklist);
			// line10--12
			extendPathCallReturn(acceptingState, acceptingState, callAlphabet, returnAlphabet, mReachabilityBridgeA,
					worklist);
		}
		
		while (!worklist.isEmpty()) {
			final StatePair workPair = worklist.dequeue();
			// line15--19
			extendAcceptingPathCallReturn(workPair.mSource, workPair.mTarget, callAlphabet, returnAlphabet,
					mReachabilityBridge, mReachabilityBridgeA, worklist);
			if (isCancellationRequested()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		
		// Reachability-C
		// Bridge reachabilityBridgeC = new Bridge();
		
		assert worklist.isEmpty();
		
		// line1--2
		copyBridge(mReachabilityBridge, mReachabilityBridgeC, worklist);
		// line3--5
		for (final STATE callPredState : allStates) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(callPredState)) {
				final STATE callSuccState = trans.getSucc();
				// TODO: xw: ill-effect of casting?
				if (!mReachabilityBridgeC.containsPair(callPredState, callSuccState)) {
					mReachabilityBridgeC.addElement(callPredState, callSuccState, new SingletonBridge(callSuccState));
					worklist.enqueue(callPredState, callSuccState);
				}
			}
		}
		
		while (!worklist.isEmpty()) {
			final StatePair workPair = worklist.dequeue();
			extendPathBeyondDestination(workPair.mSource, workPair.mTarget, mReachabilityBridgeC, worklist);
			extendPathBeyondOrigin(workPair.mSource, workPair.mTarget, mReachabilityBridgeC, worklist);
			if (isCancellationRequested()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		
		// Reachability-AC
		// Bridge reachabilityBridgeAC = new Bridge();
		
		assert worklist.isEmpty();
		
		copyBridge(mReachabilityBridgeA, mReachabilityBridgeAc, worklist);
		
		for (final STATE acceptingState : acceptingStates) {
			// line3--9
			extendAcceptingPath(acceptingState, mReachabilityBridgeC,
					mReachabilityBridgeAc, worklist);
		}
		
		// Emptiness-Check
		for (final STATE initialState : initialStates) {
			for (final STATE targetOfIntialState : mReachabilityBridgeC.getAllTargets(initialState)) {
				if (mReachabilityBridgeAc.containsPair(targetOfIntialState,
						targetOfIntialState)) {
					mWitnessInitial = initialState;
					mWitnessCritical = targetOfIntialState;
					logWitness();
					return false;
				}
			}
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info(LOG_SEPARATOR);
			mLogger.info("The NWA is empty.");
			mLogger.info(LOG_SEPARATOR);
		}
		return true;
	}
	
	private void logWitness() {
		if (mLogger.isInfoEnabled()) {
			mLogger.info(LOG_SEPARATOR);
			mLogger.info("witnessInitial: " + mWitnessInitial + ", "
					+ "witnessCritical: " + mWitnessCritical);
			mLogger.info(LOG_SEPARATOR);
		}
	}
	
	private void addReachabilityBridgeInternalPredecessors(final Worklist worklist, final Set<STATE> allStates) {
		for (final STATE internalPredState : allStates) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand
					.internalSuccessors(internalPredState)) {
				final STATE internalSuccState = trans.getSucc();
				// TODO: xw: ill-effect of casting?
				if (!mReachabilityBridge.containsPair(internalPredState, internalSuccState)) {
					mReachabilityBridge.addElement(internalPredState, internalSuccState,
							new SingletonBridge(internalSuccState));
					worklist.enqueue(internalPredState, internalSuccState);
				}
			}
		}
	}
	
	private void addReachabilityBridgeIfNotPresent(final Worklist worklist, final STATE q, final STATE p,
			final STATE pprime) {
		if (!mReachabilityBridge.containsPair(p, pprime)) {
			mReachabilityBridge.addElement(p, pprime, new QuadrupleBridge(p, q, q, pprime));
			worklist.enqueue(p, pprime);
		}
	}
	
	/**
	 * @param callSuccState
	 *            The call successor.
	 * @param callAlphabet
	 *            call alphabet
	 * @return all call predecessors of the successor through all symbols.
	 */
	public Collection<STATE> getCallPredStates(final STATE callSuccState, final Collection<LETTER> callAlphabet) {
		final Collection<STATE> callPredStates = new HashSet<>();
		for (final LETTER symbol : callAlphabet) {
			for (final IncomingCallTransition<LETTER, STATE> trans : mOperand.callPredecessors(callSuccState, symbol)) {
				callPredStates.add(trans.getPred());
			}
		}
		return callPredStates;
	}
	
	/**
	 * @param hierarcReturnPredState
	 *            The hierarchical predecessor.
	 * @param linearReturnPredState
	 *            linear predecessor
	 * @param returnAlphabet
	 *            return alphabet
	 * @return All return successors of the hierarchical return predecessor and
	 *         the linear return predecessor through all symbols.
	 */
	public Collection<STATE> getReturnSuccStates(final STATE hierarcReturnPredState, final STATE linearReturnPredState,
			final Collection<LETTER> returnAlphabet) {
		final Collection<STATE> returnSuccStates = new HashSet<>();
		for (final LETTER symbol : returnAlphabet) {
			for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(hierarcReturnPredState,
					linearReturnPredState, symbol)) {
				returnSuccStates.add(trans.getSucc());
			}
		}
		return returnSuccStates;
	}
	
	/**
	 * Returns the first internal symbol in the iteration such that
	 * "(internalPred, symbol, internalSucc)" is contained in the internal
	 * transitions.
	 */
	LETTER getFirstInternalSymbol(final STATE internalPred, final STATE internalSucc) {
		for (final LETTER internalSymbol : mOperand.lettersInternal(internalPred)) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(internalPred,
					internalSymbol)) {
				if (trans.getSucc().equals(internalSucc)) {
					return internalSymbol;
				}
			}
		}
		return null;
	}
	
	/**
	 * Returns the first call symbol in the iteration such that
	 * "(callPred, symbol, callSucc)" is contained in the call transitions.
	 */
	LETTER getFirstCallSymbol(final STATE callPred, final STATE callSucc) {
		for (final LETTER callSymbol : mOperand.lettersCall(callPred)) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(callPred, callSymbol)) {
				if (trans.getSucc().equals(callSucc)) {
					return callSymbol;
				}
			}
		}
		return null;
	}
	
	/**
	 * Returns the first return symbol in the iteration such that
	 * "(returnPredHierarc, returnPredLinear, symbol, returnSucc)"
	 * is contained in the return transitions.
	 */
	LETTER getFirstReturnSymbol(final STATE returnPredHierarc, final STATE returnPredLinear, final STATE returnSucc) {
		for (final LETTER returnSymbol : mOperand.lettersReturn(returnPredHierarc)) {
			for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(returnPredHierarc,
					returnPredLinear, returnSymbol)) {
				if (trans.getSucc().equals(returnSucc)) {
					return returnSymbol;
				}
			}
		}
		return null;
	}
	
	// TODO: xw: description?
	// [Reachability line11--13, version 2010-11-22]
	void extendPathCallReturn(final STATE origin, final STATE destination, final Collection<LETTER> callAlphabet,
			final Collection<LETTER> returnAlphabet, final Bridge reachabilityBridge, final Worklist worklist) {
		for (final STATE callPredState : getCallPredStates(origin, callAlphabet)) {
			final Collection<STATE> returnSuccStates = getReturnSuccStates(destination, callPredState, returnAlphabet);
			for (final STATE returnSuccState : returnSuccStates) {
				if (!reachabilityBridge.containsPair(callPredState, returnSuccState)) {
					final QuadrupleBridge quadrupleBridge =
							new QuadrupleBridge(callPredState, origin, destination, returnSuccState);
					reachabilityBridge.addElement(callPredState, returnSuccState, quadrupleBridge);
					worklist.enqueue(callPredState, returnSuccState);
				}
			}
		}
	}
	
	// [Reachability line14--16, version 2010-11-22]
	void extendPathBeyondDestination(final STATE origin, final STATE destination, final Bridge reachabilityBridge,
			final Worklist worklist) {
		for (final STATE stateBeyondDestination : reachabilityBridge.getAllTargets(destination)) {
			if (!reachabilityBridge.containsPair(origin, stateBeyondDestination)) {
				reachabilityBridge.addElement(origin, stateBeyondDestination, new SingletonBridge(destination));
				worklist.enqueue(origin, stateBeyondDestination);
			}
		}
	}
	
	// [Reachability line17--19, version 2010-11-22]
	void extendPathBeyondOrigin(final STATE origin, final STATE destination,
			final Bridge reachabilityBridge, final Worklist worklist) {
		for (final STATE stateBeyongdOrigin : reachabilityBridge.getAllSources(origin)) {
			if (!reachabilityBridge.containsPair(stateBeyongdOrigin, destination)) {
				reachabilityBridge.addElement(stateBeyongdOrigin, destination, new SingletonBridge(origin));
				worklist.enqueue(stateBeyongdOrigin, destination);
			}
		}
	}
	
	// [Reachability-A line3--9, version 2010-11-22]
	// TODO: xw: update version
	// TODO: xw: naming! In other words, immediate matching not included!
	void extendAcceptingPath(final STATE acceptingState, final Bridge reachabilityBridge,
			final Bridge reachabilityBridgeA, final Worklist worklist) {
		// line3--5
		if (reachabilityBridge.containsPair(acceptingState, acceptingState)
				&& (!reachabilityBridgeA.containsPair(acceptingState, acceptingState))) {
			reachabilityBridgeA.addElement(acceptingState, acceptingState, new OmegaBridge());
			worklist.enqueue(acceptingState, acceptingState);
		}
		
		// line6--9
		final Set<STATE> sourcesPlusAcceptingState = new HashSet<>();
		final Set<STATE> targetsPlusAcceptingState = new HashSet<>();
		sourcesPlusAcceptingState.add(acceptingState);
		sourcesPlusAcceptingState.addAll(reachabilityBridge.getAllSources(acceptingState));
		targetsPlusAcceptingState.add(acceptingState);
		targetsPlusAcceptingState.addAll(reachabilityBridge.getAllTargets(acceptingState));
		
		for (final STATE source : sourcesPlusAcceptingState) {
			for (final STATE target : targetsPlusAcceptingState) {
				// possible false insertion check, and, duplication check
				if (!(source == target && target == acceptingState)
						&& !(reachabilityBridgeA.containsPair(source, target))) {
					reachabilityBridgeA.addElement(source, target, new SingletonBridge(acceptingState));
					worklist.enqueue(source, target);
				}
			}
			
		}
	}
	
	// [Reachability-A line15--19, version 2010-11-22]
	// TODO: xw: make as a generalization of extendPathCallReturn?
	// TODO: xw: naming!
	void extendAcceptingPathCallReturn(final STATE origin, final STATE destination,
			final Collection<LETTER> callAlphabet, final Collection<LETTER> returnAlphabet,
			final Bridge reachabilityBridge, final Bridge reachabilityBridgeA, final Worklist worklist) {
		for (final STATE callPredState : getCallPredStates(origin, callAlphabet)) {
			for (final STATE returnSuccState : getReturnSuccStates(destination, callPredState, returnAlphabet)) {
				// TODO: xw: decision: create method for line17 and line7?
				
				final Set<STATE> sourcesPlusCallPredState = new HashSet<>();
				final Set<STATE> targetsPlusReturnSuccState = new HashSet<>();
				sourcesPlusCallPredState.add(callPredState);
				sourcesPlusCallPredState.addAll(reachabilityBridge.getAllSources(callPredState));
				targetsPlusReturnSuccState.add(returnSuccState);
				targetsPlusReturnSuccState.addAll(reachabilityBridge.getAllTargets(returnSuccState));
				
				extendAcceptingPathCallReturnHelper(origin, destination, reachabilityBridgeA, worklist, callPredState,
						returnSuccState, sourcesPlusCallPredState, targetsPlusReturnSuccState);
			}
		}
	}
	
	/**
	 * Copy the bridge to bridgeWithPendingCall and add domain of bridge to
	 * worklist.
	 */
	// Reachability-C line1--2
	// TODO: xw: naming
	void copyBridge(final Bridge bridge, final Bridge bridgeWithPendingCall, final Worklist worklist) {
		final Set<STATE> bridgeSources = bridge.getAllSources();
		if (bridgeSources != null) {
			for (final STATE source : bridgeSources) {
				final Set<STATE> bridgeTargets = bridge.getAllTargets(source);
				if (bridgeTargets == null) {
					continue;
				}
				for (final STATE target : bridgeTargets) {
					bridgeWithPendingCall.addElement(source, target, bridge.getBridgeRange(source, target));
					worklist.enqueue(source, target);
				}
			}
		}
	}
	
	@SuppressWarnings("unchecked")
	NestedRun<LETTER, STATE> reconstructionC(final STATE origin, final STATE destination) {
		// Reconstruction-C: case 4c, version 2010-12-21
		if (!mReachabilityBridgeC.containsPair(origin, destination)) {
			return new NestedRun<>(destination);
		}
		final IBridgeRange bridgeRange = mReachabilityBridgeC.getBridgeRange(origin,
				destination);
		// Reconstruction-C: case 1 and 2, version 2010-12-21
		// FIXME: xw: instance check
		if (bridgeRange instanceof BuchiIsEmptyXW.QuadrupleBridge) {
			// origin
			final STATE callPredecessor =
					((BuchiIsEmptyXW<LETTER, STATE>.QuadrupleBridge) bridgeRange).mCallPredecessor;
			final STATE callSuccessor =
					((BuchiIsEmptyXW<LETTER, STATE>.QuadrupleBridge) bridgeRange).mCallSuccessor;
			final STATE returnPredecessor =
					((BuchiIsEmptyXW<LETTER, STATE>.QuadrupleBridge) bridgeRange).mReturnPredecessor;
			// destination
			final STATE returnSuccessor =
					((BuchiIsEmptyXW<LETTER, STATE>.QuadrupleBridge) bridgeRange).mReturnSuccessor;
			
			final NestedRun<LETTER, STATE> runOfCall = new NestedRun<>(callPredecessor,
					getFirstCallSymbol(callPredecessor, callSuccessor), NestedWord.PLUS_INFINITY, callSuccessor);
			final NestedRun<LETTER, STATE> runOfReturn = new NestedRun<>(returnPredecessor,
					getFirstReturnSymbol(returnPredecessor, callPredecessor, returnSuccessor),
					NestedWord.MINUS_INFINITY, returnSuccessor);
			
			// TODO: xw: line break
			return callSuccessor == returnPredecessor
					?
					// Reconstruction-C: case 1, version 2010-12-21
					runOfCall.concatenate(runOfReturn)
					:
					// Reconstruction: case 2, version 2010-12-21
					runOfCall.concatenate(reconstructionC(callSuccessor, returnPredecessor)).concatenate(runOfReturn);
		} else if (bridgeRange instanceof BuchiIsEmptyXW.SingletonBridge) {
			// Reconstruction-C: case 3 and 4, version 2010-12-21
			final STATE singleton = ((BuchiIsEmptyXW<LETTER, STATE>.SingletonBridge) bridgeRange).mSingleton;
			// Reconstruction-C: case 4a, version 2010-12-21
			if (getFirstInternalSymbol(origin, destination) != null) {
				return new NestedRun<>(origin, getFirstInternalSymbol(origin, destination),
						NestedWord.INTERNAL_POSITION, destination);
			} else if (getFirstCallSymbol(origin, destination) != null) {
				// Reconstruction-C: case 4b, version 2010-12-21
				return new NestedRun<>(origin, getFirstCallSymbol(origin, destination), NestedWord.PLUS_INFINITY,
						destination);
			} else {
				return reconstructionC(origin, singleton).concatenate(reconstructionC(singleton, destination));
			}
		} else {
			throw new IllegalArgumentException("unsupported bridge range");
		}
	}
	
	@SuppressWarnings("unchecked")
	NestedRun<LETTER, STATE> reconstructionAc(final STATE origin, final STATE destination) {
		assert mReachabilityBridgeAc.containsPair(origin, destination) : "Pair (" + origin + ',' + destination
				+ ") not contained";
		final IBridgeRange bridgeRange = mReachabilityBridgeAc.getBridgeRange(origin, destination);
		// Reconstruction-AC: case 1, version 2010-11-22
		// TODO: xw: logical error check
		// FIXME: xw: instance check
		if (bridgeRange instanceof BuchiIsEmptyXW.OmegaBridge) {
			return reconstructionC(origin, destination);
		} else if (bridgeRange instanceof BuchiIsEmptyXW.SingletonBridge) {
			// Reconstruction-AC: case 2, version 2010-11-22
			// FIXME: xw: instance check
			final STATE singleton = ((BuchiIsEmptyXW<LETTER, STATE>.SingletonBridge) bridgeRange).mSingleton;
			// TODO: where to break the long line
			return reconstructionC(origin, singleton).concatenate(reconstructionC(singleton, destination));
		} else if (bridgeRange instanceof BuchiIsEmptyXW.QuadrupleBridge) {
			// Reconstruction-AC: case 3 and 4, version 2010-11-22
			// origin
			final STATE callPredecessor =
					((BuchiIsEmptyXW<LETTER, STATE>.QuadrupleBridge) bridgeRange).mCallPredecessor;
			final STATE callSuccessor =
					((BuchiIsEmptyXW<LETTER, STATE>.QuadrupleBridge) bridgeRange).mCallSuccessor;
			final STATE returnPredecessor =
					((BuchiIsEmptyXW<LETTER, STATE>.QuadrupleBridge) bridgeRange).mReturnPredecessor;
			// destination
			final STATE returnSuccessor =
					((BuchiIsEmptyXW<LETTER, STATE>.QuadrupleBridge) bridgeRange).mReturnSuccessor;
			
			// Reconstruction-AC: case 3, version 2010-11-22
			final NestedRun<LETTER, STATE> runOfCall = new NestedRun<>(callPredecessor,
					getFirstCallSymbol(callPredecessor, callSuccessor), NestedWord.PLUS_INFINITY,
					callSuccessor);
			final NestedRun<LETTER, STATE> runOfReturn = new NestedRun<>(returnPredecessor,
					getFirstReturnSymbol(returnPredecessor, callPredecessor, returnSuccessor),
					NestedWord.MINUS_INFINITY, returnSuccessor);
			
			// TODO: xw: breaking line
			return ((callSuccessor == returnPredecessor) && mOperand.isFinal(callSuccessor))
					?
					// Reconstruction-AC: case 3, version 2010-11-22
					reconstructionC(origin, callPredecessor).concatenate(runOfCall).concatenate(runOfReturn)
							.concatenate(reconstructionC(returnSuccessor, destination))
					:
					// Reconstruction-AC: case 4, version 2010-11-22
					reconstructionC(origin, callPredecessor).concatenate(runOfCall)
							.concatenate(reconstructionAc(callSuccessor, returnPredecessor).concatenate(runOfReturn)
									.concatenate(reconstructionC(returnSuccessor, destination)));
		}
		// TODO: xw: style: throw exception or change last else if to else?
		return null;
	}
	
	private void extendAcceptingPathCallReturnHelper(final STATE origin, final STATE destination,
			final Bridge reachabilityBridgeA, final Worklist worklist, final STATE callPredState,
			final STATE returnSuccState, final Set<STATE> sourcesPlusCallPredState,
			final Set<STATE> targetsPlusReturnSuccState) {
		for (final STATE sourceBeyondCallPredState : sourcesPlusCallPredState) {
			for (final STATE targetBeyondReturnSuccState : targetsPlusReturnSuccState) {
				if (!reachabilityBridgeA.containsPair(sourceBeyondCallPredState, targetBeyondReturnSuccState)) {
					reachabilityBridgeA.addElement(sourceBeyondCallPredState, targetBeyondReturnSuccState,
							new QuadrupleBridge(callPredState, origin, destination, returnSuccState));
					worklist.enqueue(sourceBeyondCallPredState, targetBeyondReturnSuccState);
				}
			}
		}
	}
	
	/** Element of worklist, a pair of states. */
	private class StatePair {
		private final STATE mSource;
		private final STATE mTarget;
		
		public StatePair(final STATE source, final STATE target) {
			mSource = source;
			mTarget = target;
		}
		
		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			return this.mSource == ((StatePair) obj).mSource && this.mTarget == ((StatePair) obj).mTarget;
		}
		
		@Override
		public int hashCode() {
			return (this.mSource.hashCode() + 41) * 41 + this.mTarget.hashCode();
		}
		
		@Override
		public String toString() {
			return "(" + mSource + "," + mTarget + ')';
		}
	}
	
	/** The range of bridge, can be omega, singleton or quadruple of states. */
	private interface IBridgeRange {
	}
	
	/**
	 * Omega bridge.
	 */
	private static class OmegaBridge implements IBridgeRange {
		@Override
		public String toString() {
			return "OmegaBridge";
		}
	}
	
	/**
	 * Singleton bridge.
	 * TODO: xw: naming
	 */
	private class SingletonBridge implements IBridgeRange {
		private final STATE mSingleton;
		
		public SingletonBridge(final STATE singleton) {
			this.mSingleton = singleton;
		}
		
		@Override
		public String toString() {
			return "SingletonBridge(" + mSingleton + ')';
		}
	}
	
	/**
	 * Quadruple bridge.
	 */
	private class QuadrupleBridge implements IBridgeRange {
		private final STATE mCallPredecessor;
		private final STATE mCallSuccessor;
		private final STATE mReturnPredecessor;
		private final STATE mReturnSuccessor;
		
		public QuadrupleBridge(final STATE callPredecessor, final STATE callSuccessor, final STATE returnPredecessor,
				final STATE returnSuccessor) {
			mCallPredecessor = callPredecessor;
			mCallSuccessor = callSuccessor;
			mReturnPredecessor = returnPredecessor;
			mReturnSuccessor = returnSuccessor;
		}
		
		@Override
		public String toString() {
			return "QuadrupleBridge(" + mCallPredecessor + ", " + mCallSuccessor + ", " + mReturnPredecessor + ", "
					+ mReturnSuccessor + ")";
		}
	}
	
	/** Stores the bridge of reachable pairs (source, target). */
	// TODO: xw: better naming!
	// E.g., QuadrupleBridge and Bridge are "different" things.
	private class Bridge {
		private final Map<STATE, HashMap<STATE, IBridgeRange>> mBridgeInOrder;
		private final Map<STATE, HashMap<STATE, IBridgeRange>> mBridgeReverseOrder;
		
		public Bridge() {
			mBridgeInOrder = new HashMap<>();
			mBridgeReverseOrder = new HashMap<>();
		}
		
		/** Add state pair (source, target) both in order and reverse order. */
		// TODO: xw: Decision: implement duplication check of adding same pair
		void addElement(final STATE source, final STATE target, final IBridgeRange bridgeRange) {
			assert !(mBridgeInOrder.containsKey(source) && mBridgeInOrder.get(source).containsKey(target));
			if (!mBridgeInOrder.containsKey(source)) {
				mBridgeInOrder.put(source, new HashMap<STATE, IBridgeRange>());
			}
			mBridgeInOrder.get(source).put(target, bridgeRange);
			
			assert !(mBridgeReverseOrder.containsKey(target) && mBridgeReverseOrder.get(target).containsKey(source));
			if (!mBridgeReverseOrder.containsKey(target)) {
				mBridgeReverseOrder.put(target, new HashMap<STATE, IBridgeRange>());
			}
			mBridgeReverseOrder.get(target).put(source, bridgeRange);
		}
		
		/** Get all states source. */
		Set<STATE> getAllSources() {
			if (!mBridgeInOrder.isEmpty()) {
				return mBridgeInOrder.keySet();
			}
			return Collections.emptySet();
		}
		
		/** Get all states source such that (source, target) in bridge. */
		Set<STATE> getAllSources(final STATE target) {
			if (mBridgeReverseOrder.containsKey(target)) {
				return mBridgeReverseOrder.get(target).keySet();
			}
			return Collections.emptySet();
		}
		
		/** Get all states target such that (source, target) in bridge. */
		Set<STATE> getAllTargets(final STATE source) {
			if (mBridgeInOrder.containsKey(source)) {
				return mBridgeInOrder.get(source).keySet();
			}
			return Collections.emptySet();
		}
		
		/** Get the bridge range of a pair (source, target). */
		IBridgeRange getBridgeRange(final STATE source, final STATE target) {
			if (mBridgeInOrder.containsKey(source) && mBridgeInOrder.get(source).containsKey(target)) {
				return mBridgeInOrder.get(source).get(target);
			}
			return null;
		}
		
		boolean containsPair(final STATE source, final STATE target) {
			return mBridgeInOrder.containsKey(source) && mBridgeInOrder.get(source).containsKey(target);
		}
		
		@Override
		public String toString() {
			assert mBridgeInOrder != null;
			final StringBuilder domain = new StringBuilder();
			for (final Entry<STATE, HashMap<STATE, IBridgeRange>> entry : mBridgeInOrder.entrySet()) {
				final STATE source = entry.getKey();
				for (final STATE target : entry.getValue().keySet()) {
					domain.append('(').append(source).append(',').append(target).append(") ");
				}
			}
			return domain.toString();
		}
	}
	
	/**
	 * Stores newly deduced reachable state pairs (source, target).
	 * Pair deleted after exploitation.
	 */
	private class Worklist {
		private final LinkedList<StatePair> mWorklist;
		
		public Worklist() {
			mWorklist = new LinkedList<>();
		}
		
		/** Insert a reachable pair of states (source, target) the worklist. */
		void enqueue(final STATE source, final STATE target) {
			final StatePair statePair = new StatePair(source, target);
			// assert (! worklist.contains(statePair));
			mWorklist.addLast(statePair);
		}
		
		/** Delete a reachable pair of states. */
		StatePair dequeue() {
			assert !mWorklist.isEmpty();
			return mWorklist.removeFirst();
		}
		
		/** Checks whether the worklist is empty. */
		boolean isEmpty() {
			return mWorklist.isEmpty();
		}
	}
}
