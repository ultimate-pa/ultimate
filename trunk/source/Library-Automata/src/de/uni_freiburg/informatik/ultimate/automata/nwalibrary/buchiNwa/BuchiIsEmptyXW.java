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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;


/**
 * Class that provides the Buchi emptiness check for nested word automata. 
 * 
 * @param <LETTER> Symbol. Type of the symbols used as alphabet.
 * @param <STATE> Content. Type of the labels (the content) of the automata states. 
 * @version 2010-12-18
 */
public class BuchiIsEmptyXW<LETTER,STATE> implements IOperation<LETTER,STATE> {
	private final AutomataLibraryServices mServices;
	
	public BuchiIsEmptyXW(AutomataLibraryServices services, 
			INestedWordAutomatonOldApi<LETTER, STATE> nwa) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mnwa = nwa;
		mLogger.info(startMessage());
		mResult = checkEmptiness();
		mLogger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "buchiIsEmptyXW";
	}

	@Override
	public String startMessage() {
			return "Start " + operationName() + ". Operand " + 
			mnwa.sizeInformation();	
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result is " + mResult; 
	}

	@Override
	public Boolean getResult() throws AutomataLibraryException {
		return mResult;
	}
	
	INestedWordAutomatonOldApi<LETTER, STATE> mnwa;
	final Boolean mResult;

	Bridge reachabilityBridge = new Bridge();
	Bridge reachabilityBridgeA = new Bridge();
	Bridge reachabilityBridgeC = new Bridge();
	Bridge reachabilityBridgeAC = new Bridge();
	// TODO: xw: naming
	STATE witnessInitial;
	STATE witnessCritical;

	private final ILogger mLogger;
	
	/** Element of worklist, a pair of states. */
	private class StatePair {	
		final STATE source;
		final STATE target;
		
		public StatePair(STATE source, STATE target) { 
			this.source = source;
			this.target = target;		
		}
			
		@Override
		public boolean equals(Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}			
			return (this.source == ((StatePair) obj).source && 
					this.target == ((StatePair) obj).target);
		}
		
		@Override
		public int hashCode() {
			return ((this.source.hashCode() + 41) * 41 + 
					this.target.hashCode());
		}

		@Override
		public String toString() {
			return "(" +source + ","+target +")";
		}
		
	}
	
	
    /** The range of bridge, can be omega, singleton or quadruple of states. */
	protected abstract class BridgeRange {
	}
	
	private class OmegaBridge extends BridgeRange {

		@Override
		public String toString() {
			return "OmegaBridge";
		}
		
	}
	
	// TODO: xw: naming
	private class SingletonBridge extends BridgeRange {
		final STATE singleton;
		
		public SingletonBridge(STATE singleton) {
			this.singleton = singleton;
		}

		@Override
		public String toString() {
			return "SingletonBridge(" + singleton + ")";
		}
		
		
	}
	
	private class QuadrupleBridge extends BridgeRange {
		final STATE callPredecessor;
		final STATE callSuccessor;
		final STATE returnPredecessor;
		final STATE returnSuccessor;
		
		public QuadrupleBridge(STATE callPredecessor, 
			                   STATE callSuccessor, 
				               STATE returnPredecessor, 
				               STATE returnSuccessor) {
			this.callPredecessor = callPredecessor;
			this.callSuccessor = callSuccessor;
			this.returnPredecessor = returnPredecessor;
			this.returnSuccessor = returnSuccessor;
		}

		@Override
		public String toString() {
			return "QuadrupleBridge(" 
			        + callPredecessor + ", " 
			        + callSuccessor	+ ", " 
			        + returnPredecessor + ", " 
			        + returnSuccessor + ")";
		}
	}
	
	/** Stores the bridge of reachable pairs (source, target). */
	// TODO: xw: better naming! 
	// E.g., QuadrupleBridge and Bridge are "different" things.
	private class Bridge {
		Map<STATE, HashMap<STATE, BridgeRange>> bridgeInOrder;
		Map<STATE, HashMap<STATE, BridgeRange>> 
															bridgeReverseOrder;
		
		public Bridge() {
		bridgeInOrder = 
			new HashMap<STATE, HashMap<STATE, BridgeRange>>();
		bridgeReverseOrder = 
			new HashMap<STATE, HashMap<STATE, BridgeRange>>();
		}
		
		/** Add state pair (source, target) both in order and reverse order. */
		// TODO: xw: Decision: implement duplication check of adding same pair
		void addElement(STATE source, STATE target, 
				BridgeRange bridgeRange) {
			assert (! (bridgeInOrder.containsKey(source) && 
					bridgeInOrder.get(source).containsKey(target)));
			if (! bridgeInOrder.containsKey(source)) {
				bridgeInOrder.put(source, 
						new HashMap<STATE, BridgeRange>());
			}
			bridgeInOrder.get(source).put(target, bridgeRange);

			assert (! (bridgeReverseOrder.containsKey(target) && 
					bridgeReverseOrder.get(target).containsKey(source)));
			if (! bridgeReverseOrder.containsKey(target)) {
				bridgeReverseOrder.put(target, 
						new HashMap<STATE, BridgeRange>());
			}
			bridgeReverseOrder.get(target).put(source, bridgeRange);
		}

		/** Get all states source. */
		Set<STATE> getAllSources() {
			if (! bridgeInOrder.isEmpty()) {
				return bridgeInOrder.keySet();
			} else {
				return new HashSet<STATE>(0);
			}
		}
		
		/** Get all states source such that (source, target) in bridge. */
		Set<STATE> getAllSources(STATE target) {
			if (bridgeReverseOrder.containsKey(target)) {
				return bridgeReverseOrder.get(target).keySet();
			} else {
				return new HashSet<STATE>(0);
			}
		}
		
		/** Get all states target such that (source, target) in bridge. */
		Set<STATE> getAllTargets(STATE source) {
			if (bridgeInOrder.containsKey(source)) {
				return bridgeInOrder.get(source).keySet();
			} else {
				return new HashSet<STATE>(0);
			}
		}
		
		/** Get the bridge range of a pair (source, target). */
		BridgeRange getBridgeRange(STATE source, STATE target) {
			if (bridgeInOrder.containsKey(source) && bridgeInOrder.get(source).
					containsKey(target)) {
				return bridgeInOrder.get(source).get(target);
			} else {
				return null;
			}
		}
		
		boolean containsPair(STATE source, STATE target) {
			if (bridgeInOrder.containsKey(source) && 
					bridgeInOrder.get(source).containsKey(target)) {
				return true;
			}
			return false;
		}

		@Override
		public String toString() {
			assert(bridgeInOrder != null);
			String domain = "";
			for (final STATE source : bridgeInOrder.keySet()) {
				for (final STATE target : 
										bridgeInOrder.get(source).keySet()) {
					domain = domain + "(" +source + ","+target +") ";
				}
			}
			return domain;
		}
	}
	
	/** 
	 * Stores newly deduced reachable state pairs (source, target). 
	 * Pair deleted after exploitation.
	 * */
	private class Worklist {
		public LinkedList<StatePair> worklist;
		
		public Worklist() {
			worklist = new LinkedList<StatePair>();
		}
		
		/** Insert a reachable pair of states (source, target) the worklist. */
		void enqueue(STATE source, STATE target) {
			final StatePair statePair = new StatePair(source, target); 
//			assert (! worklist.contains(statePair));
			worklist.addLast(statePair);
		}
		
		/** Delete a reachable pair of states. */
		StatePair dequeue() {
			assert (! worklist.isEmpty());
			return worklist.removeFirst();
		}
		
		/** Checks whether the worklist is empty. */
		boolean isEmpty() {
			return worklist.isEmpty();
		}	
	}
	
	public NestedLassoRun<LETTER,STATE> getAcceptingNestedLassoRun() {
		if (mResult) {
			mLogger.info("There is no accepting nested lasso run");
			return null;
		} else {
			mLogger.info("Starting construction of run");
			final NestedRun<LETTER,STATE> stem = 
				reconstructionC(witnessInitial, witnessCritical);
			final NestedRun<LETTER,STATE> loop = 
				reconstructionAC(witnessCritical, witnessCritical);
			final NestedLassoRun<LETTER,STATE> acceptingNestedLassoRun = 
										new NestedLassoRun<LETTER,STATE>(stem, loop);
			mLogger.debug("Accepting run: " + acceptingNestedLassoRun);
			mLogger.debug("Accepted word:  Stem:" + 
					acceptingNestedLassoRun.getStem().getWord() + 
					" Loop: " +
					acceptingNestedLassoRun.getLoop().getWord());
			return acceptingNestedLassoRun;
		}
	}
	
	/**
	 * Check if a Buchi nested word automaton accepts any nested lasso word. 
	 * @param nwa NestedWordAutomaton which is interpreted as Buchi nested word
	 * automaton here
	 * @return true iff nwa does not accept any nested lasso word.
	 * @throws AutomataOperationCanceledException 
	 */
	// Requires collections of transitions to be final. 
	public boolean checkEmptiness() throws AutomataLibraryException {
		final Worklist worklist = new Worklist();
		final Set<STATE> allStates = new HashSet<STATE>();
		final Set<STATE> acceptingStates = new HashSet<STATE>();
		final Set<STATE> initialStates = new HashSet<STATE>();
		final Collection<LETTER> internalAlphabet = mnwa.getInternalAlphabet();
		final Collection<LETTER> callAlphabet = mnwa.getCallAlphabet();
		final Collection<LETTER> returnAlphabet = mnwa.getReturnAlphabet();
		
		// Get all states and accepting states
		// TODO: xw: check the consequence of casting
		for (final STATE state : mnwa.getStates()) {
			allStates.add(state);
			if (mnwa.isFinal(state)) {
				acceptingStates.add(state);
			}
		}
		
		// Get all initial states
		// TODO: xw: check the consequence of casting
		for (final STATE state : mnwa.getInitialStates()) {
			initialStates.add(state);
		}
		
		// Reachability
//		Bridge reachabilityBridge = new Bridge();
		
		// line2--5
		// TODO: xw: naming?
		for (final STATE q : allStates) {
			for (final STATE p : getCallPredStates(q, callAlphabet)) {
				for (final STATE pprime : getReturnSuccStates(q, p, 
						returnAlphabet)) {
					if (! reachabilityBridge.containsPair(p, pprime)) {
						reachabilityBridge.addElement(p, pprime, 
								new QuadrupleBridge(p, q, q, pprime));
						worklist.enqueue(p, pprime);
					}
				}
			}
		}
		// line6--8
		for (final STATE internalPredState : allStates) {
			for (final LETTER symbol : internalAlphabet) {
				for (final STATE temp : 
					mnwa.succInternal(internalPredState, symbol)) {
					// TODO: xw: ill-effect of casting?
					final STATE internalSuccState = temp;
					if (! reachabilityBridge.containsPair(internalPredState, 
							internalSuccState)) {
						reachabilityBridge.addElement(internalPredState, 
								internalSuccState, 
								new SingletonBridge(internalSuccState));
						worklist.enqueue(internalPredState, internalSuccState);
					} // end if
				} // end for
			} // end for
		} //end for
		
		// line9
		while (! worklist.isEmpty()) {
			final StatePair workPair = worklist.dequeue();
			// line11--13
			extendPathCallReturn(workPair.source, workPair.target, 
					callAlphabet, returnAlphabet, reachabilityBridge, worklist);
			// line14-16
			extendPathBeyondDestination(workPair.source, workPair.target, 
					reachabilityBridge, worklist);
			// line17-19
			extendPathBeyondOrigin(workPair.source, workPair.target, 
					reachabilityBridge, worklist);
			
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}

		 
		// Reachability-A
//		Bridge reachabilityBridgeA = new Bridge();
		
		assert (worklist.isEmpty());
		for (final STATE acceptingState : acceptingStates) {
			// line3--9
			extendAcceptingPath(acceptingState, reachabilityBridge, 
					reachabilityBridgeA, worklist);
			// line10--12
			extendPathCallReturn(acceptingState, acceptingState, callAlphabet, 
					returnAlphabet, reachabilityBridgeA, worklist);
		}
		
		while (! worklist.isEmpty()) {
			final StatePair workPair = worklist.dequeue();
			// line15--19
			extendAcceptingPathCallReturn(workPair.source, workPair.target, 
					callAlphabet, returnAlphabet, reachabilityBridge, 
					reachabilityBridgeA, worklist);
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		
		
		// Reachability-C
//		Bridge reachabilityBridgeC = new Bridge();
		
		assert (worklist.isEmpty());
		
		// line1--2
		copyBridge(reachabilityBridge, reachabilityBridgeC, worklist);
		// line3--5
		for (final STATE callPredState : allStates) {
			for (final LETTER symbol : callAlphabet) {
				for (final STATE temp : 
					mnwa.succCall(callPredState, symbol)) {
					// TODO: xw: ill-effect of casting?
					final STATE callSuccState = temp;
					if (! reachabilityBridgeC.containsPair(callPredState, 
							callSuccState)) {
						reachabilityBridgeC.addElement(callPredState, 
								callSuccState, 
								new SingletonBridge(callSuccState));
						worklist.enqueue(callPredState, callSuccState);
					} // end if
				} // end for
			} // end for
		} //end for
		
		while (! worklist.isEmpty()) {
			final StatePair workPair = worklist.dequeue();
			extendPathBeyondDestination(workPair.source, workPair.target, 
					reachabilityBridgeC, worklist);
			extendPathBeyondOrigin(workPair.source,workPair.target, 
					reachabilityBridgeC, worklist);
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		
		
		// Reachability-AC
//		Bridge reachabilityBridgeAC = new Bridge();
		
		assert (worklist.isEmpty());
		
		copyBridge(reachabilityBridgeA, reachabilityBridgeAC, worklist);
		
		for (final STATE acceptingState : acceptingStates) {
			// line3--9
			extendAcceptingPath(acceptingState, reachabilityBridgeC, 
					reachabilityBridgeAC, worklist);
		}
		
		
		// Emptiness-Check
		for (final STATE initialState : initialStates) {
			for (final STATE targetOfIntialState : 
				reachabilityBridgeC.getAllTargets(initialState)) {
				if (reachabilityBridgeAC.containsPair(targetOfIntialState, 
						targetOfIntialState)) {
					witnessInitial = initialState;
					witnessCritical = targetOfIntialState;
					mLogger.info("########################################");
					mLogger.info("witnessInitial: " + witnessInitial + ", "
							+ "witnessCritical: " + witnessCritical);
					mLogger.info("########################################");
					return false;
				}
			}
		}
		mLogger.info("########################################");
		mLogger.info("The NWA is empty.");
		mLogger.info("########################################");
		return true;
	}
	
	
	/** Returns all call predecessors of the successor through all symbols. */
	public Collection<STATE> getCallPredStates(
			STATE callSuccState, Collection<LETTER> callAlphabet) {
		
		final Collection<STATE> callPredStates = new HashSet<STATE>();	
		for (final LETTER symbol : callAlphabet) {
			for (final STATE pred : mnwa.predCall(callSuccState, symbol)) {
				callPredStates.add(pred);
			}
			}
		return callPredStates;
	}
	
	
	/** Returns all return successors of the hierarchical return predecessor and 
	 *  the linear return predecessor through all symbols. 
	 * */
	@SuppressWarnings("unchecked")
	public Collection<STATE> getReturnSuccStates(
			STATE hierarcReturnPredState, 
			STATE linearReturnPredState, 
			Collection<LETTER> returnAlphabet) {
		
		final Collection<STATE> returnSuccStates= new HashSet<STATE>();	
		for (final LETTER symbol : returnAlphabet) {
			final Iterable<STATE> succs = mnwa.succReturn(hierarcReturnPredState, 
					linearReturnPredState, symbol);
			for (final STATE succ : succs) {
				returnSuccStates.add(succ);
			}
			}
		return returnSuccStates;
	}
	
	/** 
	 * Returns the first internal symbol in the iteration such that 
	 * "(internalPred, symbol, internalSucc)" is contained in the internal
	 *  transitions. */
	LETTER getFirstInternalSymbol(STATE internalPred, 
			STATE internalSucc) {
		for (final LETTER internalSymbol : mnwa.lettersInternal(internalPred)) {
			final Iterable<STATE> succs = mnwa.succInternal(internalPred,internalSymbol);
			for (final STATE succ : succs) {
				if (succ.equals(internalSucc)) {
					return internalSymbol;
				}
			}
		}
		return null;
	}

	/** 
	 * Returns the first call symbol in the iteration such that 
	 * "(callPred, symbol, callSucc)" is contained in the call transitions. */
	LETTER getFirstCallSymbol(STATE callPred, 
			STATE callSucc) {
		for (final LETTER callSymbol : mnwa.lettersCall(callPred)) {
			final Iterable<STATE> succs = mnwa.succCall(callPred, callSymbol);
			for (final STATE succ : succs) {
				if (succ.equals(callSucc)) {
					return callSymbol;
				}
			}
		}
		return null;
	}

	/** 
	 * Returns the first return symbol in the iteration such that 
	 * "(returnPredHierarc, returnPredLinear, symbol, returnSucc)" 
	 * is contained in the return transitions. */
	LETTER getFirstReturnSymbol(STATE returnPredHierarc, 
			STATE returnPredLinear,  
			STATE returnSucc) {
		for (final LETTER returnSymbol : mnwa.lettersReturn(returnPredHierarc)) {
			final Iterable<STATE> succs = mnwa.succReturn(returnPredHierarc, 
					returnPredLinear, returnSymbol);
			for (final STATE succ : succs) {
				if (succ.equals(returnSucc)) {
					return returnSymbol;
				}
			}
		}
		return null;
	}
	
	// TODO: xw: description?
	// [Reachability line11--13, version 2010-11-22]
	void extendPathCallReturn(STATE origin, STATE destination, 
			Collection<LETTER> callAlphabet, Collection<LETTER> returnAlphabet, 
			Bridge reachabilityBridge, Worklist worklist) {
		for (final STATE callPredState : getCallPredStates(origin, 
				callAlphabet)) {
			final Collection<STATE> returnSuccStates = 
				getReturnSuccStates(destination,callPredState, returnAlphabet);
			for (final STATE returnSuccState : returnSuccStates) {
				if (! reachabilityBridge.containsPair(callPredState,
															returnSuccState)) {
					final QuadrupleBridge quadrupleBridge = 
						new QuadrupleBridge(callPredState, origin, destination,
															returnSuccState);
					reachabilityBridge.addElement(callPredState, 
							returnSuccState,quadrupleBridge); 
					worklist.enqueue(callPredState, returnSuccState);
				}
			}
		}
	}
	
	
	// [Reachability line14--16, version 2010-11-22]
	void extendPathBeyondDestination(STATE origin,
									 STATE destination,
			                         Bridge reachabilityBridge,
			                         Worklist worklist) {
		for (final STATE stateBeyondDestination : reachabilityBridge.
				getAllTargets(destination)) {
			if (! reachabilityBridge.containsPair(origin,
													stateBeyondDestination)) {
				reachabilityBridge.addElement(origin, stateBeyondDestination, 
						new SingletonBridge(destination));
				worklist.enqueue(origin, stateBeyondDestination);
			}
		}	
	}

	
	// [Reachability line17--19, version 2010-11-22]
	void extendPathBeyondOrigin(STATE origin, STATE destination,
			Bridge reachabilityBridge, Worklist worklist) {
		for (final STATE stateBeyongdOrigin : reachabilityBridge.
				getAllSources(origin)) {
			if (! reachabilityBridge.containsPair(stateBeyongdOrigin,
																destination)) {
				reachabilityBridge.addElement(stateBeyongdOrigin, destination, 
						new SingletonBridge(origin));
				worklist.enqueue(stateBeyongdOrigin, destination);
			}	
		}
	}
		
	// [Reachability-A line3--9, version 2010-11-22]
	// TODO: xw: update version
	// TODO: xw: naming! In other words, immediate matching not included!
	void extendAcceptingPath(STATE acceptingState, 
			Bridge reachabilityBridge, Bridge reachabilityBridgeA, 
			Worklist worklist) {
		
		// line3--5
		if (reachabilityBridge.containsPair(acceptingState, acceptingState) 
				&& (!reachabilityBridgeA.containsPair(acceptingState, 
						acceptingState))) {
			reachabilityBridgeA.addElement(acceptingState, acceptingState, 
					new OmegaBridge());
			worklist.enqueue(acceptingState, acceptingState);
		}
		
		// line6--9
		final Set<STATE> sourcesPlusAcceptingState = 
			new HashSet<STATE>();
		final Set<STATE> targetsPlusAcceptingState = 
			new HashSet<STATE>();
		sourcesPlusAcceptingState.add(acceptingState);
		sourcesPlusAcceptingState.addAll(
				reachabilityBridge.getAllSources(acceptingState));
		targetsPlusAcceptingState.add(acceptingState);
		targetsPlusAcceptingState.addAll(
				reachabilityBridge.getAllTargets(acceptingState));
		
		for (final STATE source : sourcesPlusAcceptingState) {
			for (final STATE target : targetsPlusAcceptingState) {
				// possible false insertion check, and, duplication check
				if (! (source == target && target == acceptingState) && 
						! (reachabilityBridgeA.containsPair(source, target))) {
					reachabilityBridgeA.addElement(source, target, 
										   new SingletonBridge(acceptingState));
					worklist.enqueue(source, target);
				}
			}
			
		}
	}
	
	// [Reachability-A line15--19, version 2010-11-22]
	// TODO: xw: make as a generalization of extendPathCallReturn?
	// TODO: xw: naming!
	void extendAcceptingPathCallReturn(
			STATE origin, 
			STATE destination, 
			Collection<LETTER> callAlphabet, 
			Collection<LETTER> returnAlphabet, 
			Bridge reachabilityBridge, 
			Bridge reachabilityBridgeA, 
			Worklist worklist) {
				
		for (final STATE callPredState : getCallPredStates(origin, 
				callAlphabet)) {
			for (final STATE returnSuccState : getReturnSuccStates(
					destination, callPredState, returnAlphabet)) {
				
				// TODO: xw: decision: create method for line17 and line7?
				
				final Set<STATE> sourcesPlusCallPredState = 
					new HashSet<STATE>();
				final Set<STATE> targetsPlusReturnSuccState = 
					new HashSet<STATE>();
				sourcesPlusCallPredState.add(callPredState);
				sourcesPlusCallPredState.addAll(
						reachabilityBridge.getAllSources(callPredState));
				targetsPlusReturnSuccState.add(returnSuccState);
				targetsPlusReturnSuccState.addAll(
						reachabilityBridge.getAllTargets(returnSuccState));
				
				for (final STATE sourceBeyondCallPredState : 
					sourcesPlusCallPredState) {
					for (final STATE targetBeyondReturnSuccState : 
						targetsPlusReturnSuccState) {
						if (! reachabilityBridgeA.containsPair(
								sourceBeyondCallPredState, 
								targetBeyondReturnSuccState)) {
							reachabilityBridgeA.addElement(
									sourceBeyondCallPredState, 
									targetBeyondReturnSuccState, 
									new QuadrupleBridge(callPredState, origin, 
											destination, returnSuccState));
							worklist.enqueue(sourceBeyondCallPredState, 
									targetBeyondReturnSuccState);	
						}
					}	
				}
			}
		}
	}
	
	/** Copy the bridge to bridgeWithPendingCall and add domain of bridge to 
	 * worklist. 
	 * */
	// Reachability-C line1--2
	// TODO: xw: naming
	void copyBridge(Bridge bridge, Bridge bridgeWithPendingCall, 
			Worklist worklist) {
		final Set<STATE> bridgeSources = bridge.getAllSources();
		if (bridgeSources != null) {
			for (final STATE source : bridgeSources) {
				final Set<STATE> bridgeTargets = bridge.getAllTargets(source);
				if (bridgeTargets != null) {
					for (final STATE target : bridgeTargets) {
						bridgeWithPendingCall.addElement(source, target, 
								bridge.getBridgeRange(source, target));
						worklist.enqueue(source, target);
					}	
				}
			}	
		}		
	}
		
	NestedRun<LETTER,STATE> reconstructionC(STATE origin, 
			STATE destination) {
		// Reconstruction-C: case 4c, version 2010-12-21
		if (! reachabilityBridgeC.containsPair(origin, destination)) {
			return new NestedRun<LETTER,STATE>(destination);
		}
		final BridgeRange bridgeRange = reachabilityBridgeC.getBridgeRange(origin, 
				destination); 
		// Reconstruction-C: case 1 and 2, version 2010-12-21
		// FIXME: xw: instance check
		if (bridgeRange instanceof BuchiIsEmptyXW.QuadrupleBridge) {
			final STATE callPredecessor = 
				((BuchiIsEmptyXW<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).callPredecessor; // origin
			final STATE callSuccessor = 
				((BuchiIsEmptyXW<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).callSuccessor;
			final STATE returnPredecessor = 
				((BuchiIsEmptyXW<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).returnPredecessor; 
			final STATE returnSuccessor = 
				((BuchiIsEmptyXW<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).returnSuccessor; // destination

			final NestedRun<LETTER,STATE> runOfCall = new NestedRun<LETTER,STATE>(
					callPredecessor, 
					getFirstCallSymbol(callPredecessor, callSuccessor), 
					NestedWord.PLUS_INFINITY, 
					callSuccessor);
			final NestedRun<LETTER,STATE> runOfReturn = new NestedRun<LETTER,STATE>(
					returnPredecessor, 
					getFirstReturnSymbol(returnPredecessor, 
							callPredecessor, returnSuccessor), 
					NestedWord.MINUS_INFINITY, 
					returnSuccessor);
			
			// TODO: xw: line break
			return callSuccessor == returnPredecessor ? 
					// Reconstruction-C: case 1, version 2010-12-21
					runOfCall.concatenate(runOfReturn) :
					// Reconstruction: case 2, version 2010-12-21
					runOfCall.concatenate(
					reconstructionC(callSuccessor, 
							returnPredecessor)).concatenate(
					runOfReturn);
		} 
		// Reconstruction-C: case 3 and 4, version 2010-12-21
		else if (bridgeRange instanceof BuchiIsEmptyXW.SingletonBridge) {
			final STATE singleton = 
				((BuchiIsEmptyXW<LETTER,STATE>.SingletonBridge) 
						bridgeRange).singleton;
			// Reconstruction-C: case 4a, version 2010-12-21
			if (getFirstInternalSymbol(origin, destination) != null) {
				return new NestedRun<LETTER,STATE>(origin, getFirstInternalSymbol(origin, 
						destination), NestedWord.INTERNAL_POSITION, 
						destination);
			}
			// Reconstruction-C: case 4b, version 2010-12-21			
			else if (getFirstCallSymbol(origin, destination) != null) {
				return new NestedRun<LETTER,STATE>(origin, getFirstCallSymbol(origin, 
						destination), NestedWord.PLUS_INFINITY, 
						destination);
			} else {
				return 	reconstructionC(origin, singleton).concatenate(
						reconstructionC(singleton, destination));
			}
		}
		else {
			throw new IllegalArgumentException("unsupported bridge range");
		}
	}
	
	NestedRun<LETTER,STATE> reconstructionAC(STATE origin, 
			STATE destination) {
		assert (reachabilityBridgeAC.containsPair(origin, destination)) :
			"Pair (" + origin +"," + destination +") not contained"; 
		final BridgeRange bridgeRange = reachabilityBridgeAC.getBridgeRange(origin, 
				destination); 
		// Reconstruction-AC: case 1, version 2010-11-22
		// TODO: xw: logical error check
		// FIXME: xw: instance check
		if (bridgeRange instanceof BuchiIsEmptyXW.OmegaBridge) {
			return reconstructionC(origin, destination);
		}
		
		// Reconstruction-AC: case 2, version 2010-11-22
		// FIXME: xw: instance check
		else if (bridgeRange instanceof BuchiIsEmptyXW.SingletonBridge) {
			final STATE singleton = 
				((BuchiIsEmptyXW<LETTER,STATE>.SingletonBridge) 
						bridgeRange).singleton;
			// TODO: where to break the long line
			return reconstructionC(origin, singleton).concatenate(
					reconstructionC(singleton, destination));
		}
		// Reconstruction-AC: case 3 and 4, version 2010-11-22
		else if (bridgeRange instanceof BuchiIsEmptyXW.QuadrupleBridge) {
			final STATE callPredecessor = 
				((BuchiIsEmptyXW<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).callPredecessor; // origin
			final STATE callSuccessor = 
				((BuchiIsEmptyXW<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).callSuccessor;
			final STATE returnPredecessor = 
				((BuchiIsEmptyXW<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).returnPredecessor; 
			final STATE returnSuccessor = 
				((BuchiIsEmptyXW<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).returnSuccessor; // destination
			
			// Reconstruction-AC: case 3, version 2010-11-22
			final NestedRun<LETTER,STATE> runOfCall = new NestedRun<LETTER,STATE>(
					callPredecessor, 
					getFirstCallSymbol(callPredecessor, callSuccessor), 
					NestedWord.PLUS_INFINITY, 
					callSuccessor);
			final NestedRun<LETTER,STATE> runOfReturn = new NestedRun<LETTER,STATE>(
					returnPredecessor, 
					getFirstReturnSymbol(returnPredecessor, 
							callPredecessor, returnSuccessor), 
					NestedWord.MINUS_INFINITY, 
					returnSuccessor);
			
			// TODO: xw: breaking line
			return ((callSuccessor == returnPredecessor)
					&& mnwa.isFinal(callSuccessor))? 
					// Reconstruction-AC: case 3, version 2010-11-22
					reconstructionC(origin, callPredecessor).concatenate(
					runOfCall).concatenate(
					runOfReturn).concatenate(
					reconstructionC(returnSuccessor, destination)) :
					// Reconstruction-AC: case 4, version 2010-11-22
					reconstructionC(origin, callPredecessor).concatenate(
					runOfCall).concatenate(
					reconstructionAC(callSuccessor, 
							returnPredecessor).concatenate(
					runOfReturn).concatenate(
					reconstructionC(returnSuccessor, destination)));
		}
		// TODO: xw: style: throw exception or change last else if to else?
		return null;	
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return true;
	}



}
