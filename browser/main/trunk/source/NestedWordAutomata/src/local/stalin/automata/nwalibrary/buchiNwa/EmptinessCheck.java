package local.stalin.automata.nwalibrary.buchiNwa;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.IStateDl;
import local.stalin.automata.nwalibrary.NestedRun;
import local.stalin.automata.nwalibrary.NestedWord;
import local.stalin.core.api.StalinServices;


/**
 * Class that provides the Buchi emptiness check for nested word automata. 
 * 
 * @param <S> Symbol. Type of the symbols used as alphabet.
 * @param <C> Content. Type of the labels (the content) of the automata states. 
 * @version 2010-12-18
 */
public class EmptinessCheck<S,C> {

	Bridge reachabilityBridge = new Bridge();
	Bridge reachabilityBridgeA = new Bridge();
	Bridge reachabilityBridgeC = new Bridge();
	Bridge reachabilityBridgeAC = new Bridge();
	// TODO: xw: naming
	IStateDl<S,C> witnessInitial;
	IStateDl<S,C> witnessCritical;

	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);	
	
	/** Element of worklist, a pair of states. */
	private class StatePair {	
		final IStateDl<S,C> source;
		final IStateDl<S,C> target;
		
		public StatePair(IStateDl<S,C> source, IStateDl<S,C> target) { 
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
		final IStateDl<S,C> singleton;
		
		public SingletonBridge(IStateDl<S,C> singleton) {
			this.singleton = singleton;
		}

		@Override
		public String toString() {
			return "SingletonBridge(" + singleton + ")";
		}
		
		
	}
	
	private class QuadrupleBridge extends BridgeRange {
		final IStateDl<S,C> callPredecessor;
		final IStateDl<S,C> callSuccessor;
		final IStateDl<S,C> returnPredecessor;
		final IStateDl<S,C> returnSuccessor;
		
		public QuadrupleBridge(IStateDl<S,C> callPredecessor, 
			                   IStateDl<S,C> callSuccessor, 
				               IStateDl<S,C> returnPredecessor, 
				               IStateDl<S,C> returnSuccessor) {
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
		Map<IStateDl<S,C>, HashMap<IStateDl<S,C>, BridgeRange>> bridgeInOrder;
		Map<IStateDl<S,C>, HashMap<IStateDl<S,C>, BridgeRange>> 
															bridgeReverseOrder;
		
		public Bridge() {
		bridgeInOrder = 
			new HashMap<IStateDl<S,C>, HashMap<IStateDl<S,C>, BridgeRange>>();
		bridgeReverseOrder = 
			new HashMap<IStateDl<S,C>, HashMap<IStateDl<S,C>, BridgeRange>>();
		}
		
		/** Add state pair (source, target) both in order and reverse order. */
		// TODO: xw: Decision: implement duplication check of adding same pair
		void addElement(IStateDl<S,C> source, IStateDl<S,C> target, 
				BridgeRange bridgeRange) {
			assert (! (bridgeInOrder.containsKey(source) && 
					bridgeInOrder.get(source).containsKey(target)));
			if (! bridgeInOrder.containsKey(source)) {
				bridgeInOrder.put(source, 
						new HashMap<IStateDl<S,C>, BridgeRange>());
			}
			bridgeInOrder.get(source).put(target, bridgeRange);

			assert (! (bridgeReverseOrder.containsKey(target) && 
					bridgeReverseOrder.get(target).containsKey(source)));
			if (! bridgeReverseOrder.containsKey(target)) {
				bridgeReverseOrder.put(target, 
						new HashMap<IStateDl<S,C>, BridgeRange>());
			}
			bridgeReverseOrder.get(target).put(source, bridgeRange);
		}

		/** Get all states source. */
		Set<IStateDl<S,C>> getAllSources() {
			if (! bridgeInOrder.isEmpty()) {
				return bridgeInOrder.keySet();
			} else {
				return new HashSet<IStateDl<S,C>>(0);
			}
		}
		
		/** Get all states source such that (source, target) in bridge. */
		Set<IStateDl<S,C>> getAllSources(IStateDl<S,C> target) {
			if (bridgeReverseOrder.containsKey(target)) {
				return bridgeReverseOrder.get(target).keySet();
			} else {
				return new HashSet<IStateDl<S,C>>(0);
			}
		}
		
		/** Get all states target such that (source, target) in bridge. */
		Set<IStateDl<S,C>> getAllTargets(IStateDl<S,C> source) {
			if (bridgeInOrder.containsKey(source)) {
				return bridgeInOrder.get(source).keySet();
			} else {
				return new HashSet<IStateDl<S,C>>(0);
			}
		}
		
		/** Get the bridge range of a pair (source, target). */
		BridgeRange getBridgeRange(IStateDl<S,C> source, IStateDl<S,C> target) {
			if (bridgeInOrder.containsKey(source) && bridgeInOrder.get(source).
					containsKey(target)) {
				return bridgeInOrder.get(source).get(target);
			} else return null;
		}
		
		boolean containsPair(IStateDl<S,C> source, IStateDl<S,C> target) {
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
			for (IStateDl<S, C> source : bridgeInOrder.keySet()) {
				for (IStateDl<S, C> target : 
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
		void enqueue(IStateDl<S,C> source, IStateDl<S,C> target) {
			StatePair statePair = new StatePair(source, target); 
			assert (! worklist.contains(statePair));
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
	
	public NestedLassoRun<S,C> getAcceptingNestedLassoRun(
			INestedWordAutomaton<S,C> nwa) {
		if (! checkEmptiness(nwa)) {
			NestedRun<S,C> stem = 
				reconstructionC(witnessInitial, witnessCritical);
			NestedRun<S,C> loop = 
				reconstructionAC(witnessCritical, witnessCritical);
			NestedLassoRun<S,C> acceptingNestedLassoRun = 
										new NestedLassoRun<S,C>(stem, loop);
			s_Logger.debug("Accepting run: " + acceptingNestedLassoRun);
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
	public boolean checkEmptiness(INestedWordAutomaton<S,C> nwa) {
		Worklist worklist = new Worklist();
		Set<IStateDl<S,C>> allStates = new HashSet<IStateDl<S,C>>();
		Set<IStateDl<S,C>> acceptingStates = new HashSet<IStateDl<S,C>>();
		Set<IStateDl<S,C>> initialStates = new HashSet<IStateDl<S,C>>();
		Collection<S> internalAlphabet = nwa.getInternalAlphabet();
		Collection<S> callAlphabet = nwa.getCallAlphabet();
		Collection<S> returnAlphabet = nwa.getReturnAlphabet();
		
		// Get all states and accepting states
		// TODO: xw: check the consequence of casting
		for (IState<S,C> state : nwa.getAllStates()) {
			allStates.add((IStateDl<S,C>) state);
			if (state.isFinal()) {
				acceptingStates.add((IStateDl<S,C>) state);
			}
		}
		
		// Get all initial states
		// TODO: xw: check the consequence of casting
		for (IState<S,C> state : nwa.getInitialStates()) {
			initialStates.add((IStateDl<S,C>) state);
		}
		
		// Reachability
//		Bridge reachabilityBridge = new Bridge();
		
		// line2--5
		// TODO: xw: naming?
		for (IStateDl<S,C> q : allStates) {
			for (IStateDl<S,C> p : getCallPredStates(q, callAlphabet)) {
				for (IStateDl<S,C> pprime : getReturnSuccStates(q, p, 
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
		for (IStateDl<S,C> internalPredState : allStates) {
			for (S symbol : internalAlphabet) {
				for (IState<S,C> temp : 
					internalPredState.getInternalSucc(symbol)) {
					// TODO: xw: ill-effect of casting?
					IStateDl<S,C> internalSuccState = (IStateDl<S,C>) temp;
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
		for (IStateDl<S,C> acceptingState : acceptingStates) {
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
		for (IStateDl<S,C> callPredState : allStates) {
			for (S symbol : callAlphabet) {
				for (IState<S,C> temp : 
					callPredState.getCallSucc(symbol)) {
					// TODO: xw: ill-effect of casting?
					IStateDl<S,C> callSuccState = (IStateDl<S,C>) temp;
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
		
		for (IStateDl<S,C> acceptingState : acceptingStates) {
			// line3--9
			extendAcceptingPath(acceptingState, reachabilityBridgeC, 
					reachabilityBridgeAC, worklist);
		}
		
		
		// Emptiness-Check
		for (IStateDl<S,C> initialState : initialStates) {
			for (IStateDl<S,C> targetOfIntialState : 
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
	public Collection<IStateDl<S,C>> getCallPredStates(
			IStateDl<S,C> callSuccState, Collection<S> callAlphabet) {
		
		Collection<IStateDl<S,C>> callPredStates = new HashSet<IStateDl<S,C>>();	
		for (S symbol : callAlphabet) {
			callPredStates.addAll(callSuccState.getInCall(symbol));
			}
		return callPredStates;
	}
	
	
	/** Returns all return successors of the hierarchical return predecessor and 
	 *  the linear return predecessor through all symbols. 
	 * */
	@SuppressWarnings("unchecked")
	public Collection<IStateDl<S,C>> getReturnSuccStates(
			IStateDl<S,C> hierarcReturnPredState, 
			IStateDl<S,C> linearReturnPredState, 
			Collection<S> returnAlphabet) {
		
		Collection<IStateDl<S,C>> returnSuccStates= new HashSet<IStateDl<S,C>>();	
		for (S symbol : returnAlphabet) {
			returnSuccStates.addAll((Collection<? extends IStateDl<S,C>>) 
					hierarcReturnPredState.getReturnSucc(linearReturnPredState, 
							symbol));
			}
		return returnSuccStates;
	}
	
	/** 
	 * Returns the first internal symbol in the iteration such that 
	 * "(internalPred, symbol, internalSucc)" is contained in the internal
	 *  transitions. */
	S getFirstInternalSymbol(IStateDl<S,C> internalPred, 
			IStateDl<S,C> internalSucc) {
		for (S internalSymbol : internalPred.getSymbolsInternal()) {
			if (internalPred.getInternalSucc(internalSymbol).
													contains(internalSucc)) {
				return internalSymbol;
			}
		}
		return null;
	}

	/** 
	 * Returns the first call symbol in the iteration such that 
	 * "(callPred, symbol, callSucc)" is contained in the call transitions. */
	S getFirstCallSymbol(IStateDl<S,C> callPred, 
			IStateDl<S,C> callSucc) {
		for (S callSymbol : callPred.getSymbolsCall()) {
			if (callPred.getCallSucc(callSymbol).contains(callSucc)) {
				return callSymbol;
			}
		}
		return null;
	}

	/** 
	 * Returns the first return symbol in the iteration such that 
	 * "(returnPredHierarc, returnPredLinear, symbol, returnSucc)" 
	 * is contained in the return transitions. */
	S getFirstReturnSymbol(IStateDl<S,C> returnPredHierarc, 
			IStateDl<S,C> returnPredLinear,  
			IStateDl<S,C> returnSucc) {
		for (S returnSymbol : returnPredHierarc.getSymbolsReturn()) {
			if (returnPredHierarc.getReturnSucc(returnPredLinear, 
					returnSymbol).contains(returnSucc)) {
				return returnSymbol;
			}
		}
		return null;
	}
	
	// TODO: xw: description?
	// [Reachability line11--13, version 2010-11-22]
	void extendPathCallReturn(IStateDl<S,C> origin, IStateDl<S,C> destination, 
			Collection<S> callAlphabet, Collection<S> returnAlphabet, 
			Bridge reachabilityBridge, Worklist worklist) {
		for (IStateDl<S,C> callPredState : getCallPredStates(origin, 
				callAlphabet)) {
			Collection<IStateDl<S, C>> returnSuccStates = 
				getReturnSuccStates(destination,callPredState, returnAlphabet);
			for (IStateDl<S,C> returnSuccState : returnSuccStates) {
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
	void extendPathBeyondDestination(IStateDl<S,C> origin,
									 IStateDl<S,C> destination,
			                         Bridge reachabilityBridge,
			                         Worklist worklist) {
		for (IStateDl<S,C> stateBeyondDestination : reachabilityBridge.
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
	void extendPathBeyondOrigin(IStateDl<S,C> origin, IStateDl<S,C> destination,
			Bridge reachabilityBridge, Worklist worklist) {
		for (IStateDl<S,C> stateBeyongdOrigin : reachabilityBridge.
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
	void extendAcceptingPath(IStateDl<S,C> acceptingState, 
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
		Set<IStateDl<S,C>> sourcesPlusAcceptingState = 
			new HashSet<IStateDl<S,C>>();
		Set<IStateDl<S,C>> targetsPlusAcceptingState = 
			new HashSet<IStateDl<S,C>>();
		sourcesPlusAcceptingState.add(acceptingState);
		sourcesPlusAcceptingState.addAll(
				reachabilityBridge.getAllSources(acceptingState));
		targetsPlusAcceptingState.add(acceptingState);
		targetsPlusAcceptingState.addAll(
				reachabilityBridge.getAllTargets(acceptingState));
		
		for (IStateDl<S,C> source : sourcesPlusAcceptingState) {
			for (IStateDl<S,C> target : targetsPlusAcceptingState) {
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
			IStateDl<S,C> origin, 
			IStateDl<S,C> destination, 
			Collection<S> callAlphabet, 
			Collection<S> returnAlphabet, 
			Bridge reachabilityBridge, 
			Bridge reachabilityBridgeA, 
			Worklist worklist) {
				
		for (IStateDl<S,C> callPredState : getCallPredStates(origin, 
				callAlphabet)) {
			for (IStateDl<S,C> returnSuccState : getReturnSuccStates(
					destination, callPredState, returnAlphabet)) {
				
				// TODO: xw: decision: create method for line17 and line7?
				
				Set<IStateDl<S,C>> sourcesPlusCallPredState = 
					new HashSet<IStateDl<S,C>>();
				Set<IStateDl<S,C>> targetsPlusReturnSuccState = 
					new HashSet<IStateDl<S,C>>();
				sourcesPlusCallPredState.add(callPredState);
				sourcesPlusCallPredState.addAll(
						reachabilityBridge.getAllSources(callPredState));
				targetsPlusReturnSuccState.add(returnSuccState);
				targetsPlusReturnSuccState.addAll(
						reachabilityBridge.getAllTargets(returnSuccState));
				
				for (IStateDl<S,C> sourceBeyondCallPredState : 
					sourcesPlusCallPredState) {
					for (IStateDl<S,C> targetBeyondReturnSuccState : 
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
		Set<IStateDl<S,C>> bridgeSources = bridge.getAllSources();
		if (bridgeSources != null) {
			for (IStateDl<S,C> source : bridgeSources) {
				Set<IStateDl<S,C>> bridgeTargets = bridge.getAllTargets(source);
				if (bridgeTargets != null) {
					for (IStateDl<S,C> target : bridgeTargets) {
						bridgeWithPendingCall.addElement(source, target, 
								bridge.getBridgeRange(source, target));
						worklist.enqueue(source, target);
					}	
				}
			}	
		}		
	}
		
	NestedRun<S,C> reconstructionC(IStateDl<S,C> origin, 
			IStateDl<S,C> destination) {
		// Reconstruction-C: case 4c, version 2010-12-21
		if (! reachabilityBridgeC.containsPair(origin, destination)) {
			return new NestedRun<S,C>(destination);
		}
		BridgeRange bridgeRange = reachabilityBridgeC.getBridgeRange(origin, 
				destination); 
		// Reconstruction-C: case 1 and 2, version 2010-12-21
		// FIXME: xw: instance check
		if (bridgeRange instanceof EmptinessCheck.QuadrupleBridge) {
			IStateDl<S,C> callPredecessor = 
				((EmptinessCheck<S,C>.QuadrupleBridge) 
						bridgeRange).callPredecessor; // origin
			IStateDl<S,C> callSuccessor = 
				((EmptinessCheck<S,C>.QuadrupleBridge) 
						bridgeRange).callSuccessor;
			IStateDl<S,C> returnPredecessor = 
				((EmptinessCheck<S,C>.QuadrupleBridge) 
						bridgeRange).returnPredecessor; 
			IStateDl<S,C> returnSuccessor = 
				((EmptinessCheck<S,C>.QuadrupleBridge) 
						bridgeRange).returnSuccessor; // destination

			NestedRun<S,C> runOfCall = new NestedRun<S,C>(
					callPredecessor, 
					getFirstCallSymbol(callPredecessor, callSuccessor), 
					NestedWord.PLUS_INFINITY, 
					callSuccessor);
			NestedRun<S,C> runOfReturn = new NestedRun<S,C>(
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
			IStateDl<S,C> singleton = 
				((EmptinessCheck<S,C>.SingletonBridge) 
						bridgeRange).singleton;
			// Reconstruction-C: case 4a, version 2010-12-21
			if (getFirstInternalSymbol(origin, destination) != null) {
				return new NestedRun<S,C>(origin, getFirstInternalSymbol(origin, 
						destination), NestedWord.INTERNAL_POSITION, 
						destination);
			}
			// Reconstruction-C: case 4b, version 2010-12-21			
			else if (getFirstCallSymbol(origin, destination) != null) {
				return new NestedRun<S,C>(origin, getFirstCallSymbol(origin, 
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
	
	NestedRun<S,C> reconstructionAC(IStateDl<S,C> origin, 
			IStateDl<S,C> destination) {
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
			IStateDl<S,C> singleton = 
				((EmptinessCheck<S,C>.SingletonBridge) 
						bridgeRange).singleton;
			// TODO: where to break the long line
			return reconstructionC(origin, singleton).concatenate(
					reconstructionC(singleton, destination));
		}
		// Reconstruction-AC: case 3 and 4, version 2010-11-22
		else if (bridgeRange instanceof EmptinessCheck.QuadrupleBridge) {
			IStateDl<S,C> callPredecessor = 
				((EmptinessCheck<S,C>.QuadrupleBridge) 
						bridgeRange).callPredecessor; // origin
			IStateDl<S,C> callSuccessor = 
				((EmptinessCheck<S,C>.QuadrupleBridge) 
						bridgeRange).callSuccessor;
			IStateDl<S,C> returnPredecessor = 
				((EmptinessCheck<S,C>.QuadrupleBridge) 
						bridgeRange).returnPredecessor; 
			IStateDl<S,C> returnSuccessor = 
				((EmptinessCheck<S,C>.QuadrupleBridge) 
						bridgeRange).returnSuccessor; // destination
			
			// Reconstruction-AC: case 3, version 2010-11-22
			NestedRun<S,C> runOfCall = new NestedRun<S,C>(
					callPredecessor, 
					getFirstCallSymbol(callPredecessor, callSuccessor), 
					NestedWord.PLUS_INFINITY, 
					callSuccessor);
			NestedRun<S,C> runOfReturn = new NestedRun<S,C>(
					returnPredecessor, 
					getFirstReturnSymbol(returnPredecessor, 
							callPredecessor, returnSuccessor), 
					NestedWord.MINUS_INFINITY, 
					returnSuccessor);
			
			// TODO: xw: breaking line
			return ((callSuccessor == returnPredecessor)
					&& callSuccessor.isFinal())? 
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
