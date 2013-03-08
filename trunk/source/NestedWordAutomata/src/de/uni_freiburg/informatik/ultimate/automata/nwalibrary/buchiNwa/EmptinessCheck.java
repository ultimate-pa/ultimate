package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


/**
 * Class that provides the Buchi emptiness check for nested word automata. 
 * 
 * @param <LETTER> Symbol. Type of the symbols used as alphabet.
 * @param <STATE> Content. Type of the labels (the content) of the automata states. 
 * @version 2010-12-18
 */
public class EmptinessCheck<LETTER,STATE> {
	
	NestedWordAutomaton<LETTER, STATE> m_nwa;

	Bridge reachabilityBridge = new Bridge();
	Bridge reachabilityBridgeA = new Bridge();
	Bridge reachabilityBridgeC = new Bridge();
	Bridge reachabilityBridgeAC = new Bridge();
	// TODO: xw: naming
	STATE witnessInitial;
	STATE witnessCritical;

	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);	
	
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
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;			
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
			} else return null;
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
			for (STATE source : bridgeInOrder.keySet()) {
				for (STATE target : 
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
			StatePair statePair = new StatePair(source, target); 
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
	
	public NestedLassoRun<LETTER,STATE> getAcceptingNestedLassoRun(
			INestedWordAutomaton<LETTER,STATE> nwa) {
		s_Logger.info("Starting emptiness test. Operand" + 
				((NestedWordAutomaton) nwa).sizeInformation());
		if (! checkEmptiness(nwa)) {
			NestedRun<LETTER,STATE> stem = 
				reconstructionC(witnessInitial, witnessCritical);
			NestedRun<LETTER,STATE> loop = 
				reconstructionAC(witnessCritical, witnessCritical);
			NestedLassoRun<LETTER,STATE> acceptingNestedLassoRun = 
										new NestedLassoRun<LETTER,STATE>(stem, loop);
			s_Logger.debug("Accepting run: " + acceptingNestedLassoRun);
			s_Logger.debug("Accepted word:  Stem:" + 
					acceptingNestedLassoRun.getStem().getWord() + 
					" Loop: " +
					acceptingNestedLassoRun.getLoop().getWord());
			return acceptingNestedLassoRun;
		}
		return null;
	}
	
	/**
	 * Check if a Buchi nested word automaton accepts any nested lasso word. 
	 * @param nwa NestedWordAutomaton which is interpreted as Buchi nested word
	 * automaton here
	 * @return true iff nwa does not accept any nested lasso word.
	 */
	// Requires collections of transitions to be final. 
	public boolean checkEmptiness(INestedWordAutomaton<LETTER,STATE> nwa) {
		m_nwa = (NestedWordAutomaton<LETTER, STATE>) nwa;
		Worklist worklist = new Worklist();
		Set<STATE> allStates = new HashSet<STATE>();
		Set<STATE> acceptingStates = new HashSet<STATE>();
		Set<STATE> initialStates = new HashSet<STATE>();
		Collection<LETTER> internalAlphabet = nwa.getInternalAlphabet();
		Collection<LETTER> callAlphabet = nwa.getCallAlphabet();
		Collection<LETTER> returnAlphabet = nwa.getReturnAlphabet();
		
		// Get all states and accepting states
		// TODO: xw: check the consequence of casting
		for (STATE state : nwa.getStates()) {
			allStates.add((STATE) state);
			if (nwa.isFinal(state)) {
				acceptingStates.add((STATE) state);
			}
		}
		
		// Get all initial states
		// TODO: xw: check the consequence of casting
		for (STATE state : nwa.getInitialStates()) {
			initialStates.add((STATE) state);
		}
		
		// Reachability
//		Bridge reachabilityBridge = new Bridge();
		
		// line2--5
		// TODO: xw: naming?
		for (STATE q : allStates) {
			for (STATE p : getCallPredStates(q, callAlphabet)) {
				for (STATE pprime : getReturnSuccStates(q, p, 
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
		for (STATE internalPredState : allStates) {
			for (LETTER symbol : internalAlphabet) {
				for (STATE temp : 
					nwa.succInternal(internalPredState, symbol)) {
					// TODO: xw: ill-effect of casting?
					STATE internalSuccState = (STATE) temp;
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
			StatePair workPair = worklist.dequeue();
			// line11--13
			extendPathCallReturn(workPair.source, workPair.target, 
					callAlphabet, returnAlphabet, reachabilityBridge, worklist);
			// line14-16
			extendPathBeyondDestination(workPair.source, workPair.target, 
					reachabilityBridge, worklist);
			// line17-19
			extendPathBeyondOrigin(workPair.source, workPair.target, 
					reachabilityBridge, worklist);
		}

		 
		// Reachability-A
//		Bridge reachabilityBridgeA = new Bridge();
		
		assert (worklist.isEmpty());
		for (STATE acceptingState : acceptingStates) {
			// line3--9
			extendAcceptingPath(acceptingState, reachabilityBridge, 
					reachabilityBridgeA, worklist);
			// line10--12
			extendPathCallReturn(acceptingState, acceptingState, callAlphabet, 
					returnAlphabet, reachabilityBridgeA, worklist);
		}
		
		while (! worklist.isEmpty()) {
			StatePair workPair = worklist.dequeue();
			// line15--19
			extendAcceptingPathCallReturn(workPair.source, workPair.target, 
					callAlphabet, returnAlphabet, reachabilityBridge, 
					reachabilityBridgeA, worklist);
		}
		
		
		// Reachability-C
//		Bridge reachabilityBridgeC = new Bridge();
		
		assert (worklist.isEmpty());
		
		// line1--2
		copyBridge(reachabilityBridge, reachabilityBridgeC, worklist);
		// line3--5
		for (STATE callPredState : allStates) {
			for (LETTER symbol : callAlphabet) {
				for (STATE temp : 
					nwa.succCall(callPredState, symbol)) {
					// TODO: xw: ill-effect of casting?
					STATE callSuccState = (STATE) temp;
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
			StatePair workPair = worklist.dequeue();
			extendPathBeyondDestination(workPair.source, workPair.target, 
					reachabilityBridgeC, worklist);
			extendPathBeyondOrigin(workPair.source,workPair.target, 
					reachabilityBridgeC, worklist);
		}
		
		
		// Reachability-AC
//		Bridge reachabilityBridgeAC = new Bridge();
		
		assert (worklist.isEmpty());
		
		copyBridge(reachabilityBridgeA, reachabilityBridgeAC, worklist);
		
		for (STATE acceptingState : acceptingStates) {
			// line3--9
			extendAcceptingPath(acceptingState, reachabilityBridgeC, 
					reachabilityBridgeAC, worklist);
		}
		
		
		// Emptiness-Check
		for (STATE initialState : initialStates) {
			for (STATE targetOfIntialState : 
				reachabilityBridgeC.getAllTargets(initialState)) {
				if (reachabilityBridgeAC.containsPair(targetOfIntialState, 
						targetOfIntialState)) {
					witnessInitial = initialState;
					witnessCritical = targetOfIntialState;
					s_Logger.info("########################################");
					s_Logger.info("witnessInitial: " + witnessInitial + ", "
							+ "witnessCritical: " + witnessCritical);
					s_Logger.info("########################################");
					return false;
				}
			}
		}
		s_Logger.info("########################################");
		s_Logger.info("The NWA is empty.");
		s_Logger.info("########################################");
		return true;
	}
	
	
	/** Returns all call predecessors of the successor through all symbols. */
	public Collection<STATE> getCallPredStates(
			STATE callSuccState, Collection<LETTER> callAlphabet) {
		
		Collection<STATE> callPredStates = new HashSet<STATE>();	
		for (LETTER symbol : callAlphabet) {
			callPredStates.addAll(m_nwa.predCall(callSuccState, symbol));
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
		
		Collection<STATE> returnSuccStates= new HashSet<STATE>();	
		for (LETTER symbol : returnAlphabet) {
			Collection<STATE> succs = m_nwa.succReturn(hierarcReturnPredState, 
					linearReturnPredState, symbol);
			returnSuccStates.addAll(succs);
			}
		return returnSuccStates;
	}
	
	/** 
	 * Returns the first internal symbol in the iteration such that 
	 * "(internalPred, symbol, internalSucc)" is contained in the internal
	 *  transitions. */
	LETTER getFirstInternalSymbol(STATE internalPred, 
			STATE internalSucc) {
		for (LETTER internalSymbol : m_nwa.lettersInternal(internalPred)) {
			Collection<STATE> succs = m_nwa.succInternal(internalPred,internalSymbol);
			if (succs. contains(internalSucc)) {
				return internalSymbol;
			}
		}
		return null;
	}

	/** 
	 * Returns the first call symbol in the iteration such that 
	 * "(callPred, symbol, callSucc)" is contained in the call transitions. */
	LETTER getFirstCallSymbol(STATE callPred, 
			STATE callSucc) {
		for (LETTER callSymbol : m_nwa.lettersCall(callPred)) {
			Collection<STATE> succs = m_nwa.succCall(callPred, callSymbol);
			if (succs.contains(callSucc)) {
				return callSymbol;
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
		for (LETTER returnSymbol : m_nwa.lettersReturn(returnPredHierarc)) {
			Collection<STATE> succs = m_nwa.succReturn(returnPredHierarc, 
					returnPredLinear, returnSymbol);
			if (succs.contains(returnSucc)) {
				return returnSymbol;
			}
		}
		return null;
	}
	
	// TODO: xw: description?
	// [Reachability line11--13, version 2010-11-22]
	void extendPathCallReturn(STATE origin, STATE destination, 
			Collection<LETTER> callAlphabet, Collection<LETTER> returnAlphabet, 
			Bridge reachabilityBridge, Worklist worklist) {
		for (STATE callPredState : getCallPredStates(origin, 
				callAlphabet)) {
			Collection<STATE> returnSuccStates = 
				getReturnSuccStates(destination,callPredState, returnAlphabet);
			for (STATE returnSuccState : returnSuccStates) {
				if (! reachabilityBridge.containsPair(callPredState,
															returnSuccState)) {
					QuadrupleBridge quadrupleBridge = 
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
		for (STATE stateBeyondDestination : reachabilityBridge.
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
		for (STATE stateBeyongdOrigin : reachabilityBridge.
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
		Set<STATE> sourcesPlusAcceptingState = 
			new HashSet<STATE>();
		Set<STATE> targetsPlusAcceptingState = 
			new HashSet<STATE>();
		sourcesPlusAcceptingState.add(acceptingState);
		sourcesPlusAcceptingState.addAll(
				reachabilityBridge.getAllSources(acceptingState));
		targetsPlusAcceptingState.add(acceptingState);
		targetsPlusAcceptingState.addAll(
				reachabilityBridge.getAllTargets(acceptingState));
		
		for (STATE source : sourcesPlusAcceptingState) {
			for (STATE target : targetsPlusAcceptingState) {
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
				
		for (STATE callPredState : getCallPredStates(origin, 
				callAlphabet)) {
			for (STATE returnSuccState : getReturnSuccStates(
					destination, callPredState, returnAlphabet)) {
				
				// TODO: xw: decision: create method for line17 and line7?
				
				Set<STATE> sourcesPlusCallPredState = 
					new HashSet<STATE>();
				Set<STATE> targetsPlusReturnSuccState = 
					new HashSet<STATE>();
				sourcesPlusCallPredState.add(callPredState);
				sourcesPlusCallPredState.addAll(
						reachabilityBridge.getAllSources(callPredState));
				targetsPlusReturnSuccState.add(returnSuccState);
				targetsPlusReturnSuccState.addAll(
						reachabilityBridge.getAllTargets(returnSuccState));
				
				for (STATE sourceBeyondCallPredState : 
					sourcesPlusCallPredState) {
					for (STATE targetBeyondReturnSuccState : 
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
		Set<STATE> bridgeSources = bridge.getAllSources();
		if (bridgeSources != null) {
			for (STATE source : bridgeSources) {
				Set<STATE> bridgeTargets = bridge.getAllTargets(source);
				if (bridgeTargets != null) {
					for (STATE target : bridgeTargets) {
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
		BridgeRange bridgeRange = reachabilityBridgeC.getBridgeRange(origin, 
				destination); 
		// Reconstruction-C: case 1 and 2, version 2010-12-21
		// FIXME: xw: instance check
		if (bridgeRange instanceof EmptinessCheck.QuadrupleBridge) {
			STATE callPredecessor = 
				((EmptinessCheck<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).callPredecessor; // origin
			STATE callSuccessor = 
				((EmptinessCheck<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).callSuccessor;
			STATE returnPredecessor = 
				((EmptinessCheck<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).returnPredecessor; 
			STATE returnSuccessor = 
				((EmptinessCheck<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).returnSuccessor; // destination

			NestedRun<LETTER,STATE> runOfCall = new NestedRun<LETTER,STATE>(
					callPredecessor, 
					getFirstCallSymbol(callPredecessor, callSuccessor), 
					NestedWord.PLUS_INFINITY, 
					callSuccessor);
			NestedRun<LETTER,STATE> runOfReturn = new NestedRun<LETTER,STATE>(
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
		else if (bridgeRange instanceof EmptinessCheck.SingletonBridge) {
			STATE singleton = 
				((EmptinessCheck<LETTER,STATE>.SingletonBridge) 
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
			}
			else 
				return 	reconstructionC(origin, singleton).concatenate(
						reconstructionC(singleton, destination));
		}
		else {
			throw new IllegalArgumentException("unsupported bridge range");
		}
	}
	
	NestedRun<LETTER,STATE> reconstructionAC(STATE origin, 
			STATE destination) {
		assert (reachabilityBridgeAC.containsPair(origin, destination)) :
			"Pair (" + origin +"," + destination +") not contained"; 
		BridgeRange bridgeRange = reachabilityBridgeAC.getBridgeRange(origin, 
				destination); 
		// Reconstruction-AC: case 1, version 2010-11-22
		// TODO: xw: logical error check
		// FIXME: xw: instance check
		if (bridgeRange instanceof EmptinessCheck.OmegaBridge) {
			return reconstructionC(origin, destination);
		}
		
		// Reconstruction-AC: case 2, version 2010-11-22
		// FIXME: xw: instance check
		else if (bridgeRange instanceof EmptinessCheck.SingletonBridge) {
			STATE singleton = 
				((EmptinessCheck<LETTER,STATE>.SingletonBridge) 
						bridgeRange).singleton;
			// TODO: where to break the long line
			return reconstructionC(origin, singleton).concatenate(
					reconstructionC(singleton, destination));
		}
		// Reconstruction-AC: case 3 and 4, version 2010-11-22
		else if (bridgeRange instanceof EmptinessCheck.QuadrupleBridge) {
			STATE callPredecessor = 
				((EmptinessCheck<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).callPredecessor; // origin
			STATE callSuccessor = 
				((EmptinessCheck<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).callSuccessor;
			STATE returnPredecessor = 
				((EmptinessCheck<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).returnPredecessor; 
			STATE returnSuccessor = 
				((EmptinessCheck<LETTER,STATE>.QuadrupleBridge) 
						bridgeRange).returnSuccessor; // destination
			
			// Reconstruction-AC: case 3, version 2010-11-22
			NestedRun<LETTER,STATE> runOfCall = new NestedRun<LETTER,STATE>(
					callPredecessor, 
					getFirstCallSymbol(callPredecessor, callSuccessor), 
					NestedWord.PLUS_INFINITY, 
					callSuccessor);
			NestedRun<LETTER,STATE> runOfReturn = new NestedRun<LETTER,STATE>(
					returnPredecessor, 
					getFirstReturnSymbol(returnPredecessor, 
							callPredecessor, returnSuccessor), 
					NestedWord.MINUS_INFINITY, 
					returnSuccessor);
			
			// TODO: xw: breaking line
			return ((callSuccessor == returnPredecessor)
					&& m_nwa.isFinal(callSuccessor))? 
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

}
