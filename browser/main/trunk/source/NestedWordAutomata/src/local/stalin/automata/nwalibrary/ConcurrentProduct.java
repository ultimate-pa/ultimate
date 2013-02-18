package local.stalin.automata.nwalibrary;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import local.stalin.automata.Activator;
import local.stalin.core.api.StalinServices;

import org.apache.log4j.Logger;


/**
 * Given a PetriNet, constructs a finite Automaton that recognizes the same
 * language.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Symbol
 * @param <C> Content
 */
public class ConcurrentProduct<S,C> {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final boolean m_ConcurrentPrefixProduct;

	private final INestedWordAutomaton<S,C> M_Nwa1;
	private final INestedWordAutomaton<S,C> M_Nwa2;
	private final INestedWordAutomaton<S,C> m_Result;
	
	/**
	 * List of state pairs from the input automata for which
	 * <ul>
	 * <li> there has already been a state in the result constructed
	 * <li> outgoing transitions of this state have not yet been constructed.
	 * </ul>
 	 */
	private final StatePairQueue m_Worklist = new StatePairQueue();
	
	/**
	 * Map from state pairs of the input automata to corresponding states
	 * in the result automaton. 
	 */
	private final StatePair2StateMap inputPair2resultState = 
		new StatePair2StateMap();
	

	/**
	 * Common symbols of the Alphabets of the input automata.
	 */
	private final HashSet<S> m_SynchronizationAlphabet;

	private final ContentFactory<C> m_ContentFactory;
	

	

	
	
	/**
	 * Returns the automaton state that represents the state pair
	 * (state1,state2). If this state is not yet constructed, construct it
	 * and enqueue the pair (state1,state2). If it has to be
	 * constructed it is an initial state iff isInitial is true. 
	 */
	private IState<S,C> getState(IState<S,C> state1, IState<S,C> state2,
															boolean isInitial) {
		IState<S,C> state = 
					inputPair2resultState.get(state1, state2);
		if (state == null) {
			boolean isFinal;
			if (m_ConcurrentPrefixProduct) {
				isFinal = state1.isFinal() || state2.isFinal();
			}
			else {			
				isFinal = state1.isFinal() && state2.isFinal();
			}
			C content1 = state1.getContent();
			C content2 = state2.getContent();
			C content = m_ContentFactory.getContentOnConcurrentProduct(
															content1,content2);
			state = m_Result.addState(isInitial, isFinal,content);
			inputPair2resultState.put(state1,state2,state);
			m_Worklist.enqueue(state1, state2);
		}
		return state;
	}
	

	
	
	private void constructOutgoingTransitions(IState<S,C> state1,
			IState<S,C> state2) {
		IState<S,C> state = getState(state1,state2,false);
		HashSet<S> commonOutSymbols = 
			new HashSet<S>(state1.getSymbolsInternal());
		commonOutSymbols.retainAll(state2.getSymbolsInternal());
		HashSet<S> state1OnlySymbols = 
			new HashSet<S>(state1.getSymbolsInternal());
		state1OnlySymbols.removeAll(m_SynchronizationAlphabet);
		HashSet<S> state2OnlySymbols = 
			new HashSet<S>(state2.getSymbolsInternal());
		state2OnlySymbols.removeAll(m_SynchronizationAlphabet);
		
		for (S symbol : commonOutSymbols) {
			Collection<IState<S,C>> succ1s = state1.getInternalSucc(symbol);
			Collection<IState<S,C>> succ2s = state2.getInternalSucc(symbol);
			for (IState<S,C> succ1 : succ1s) {
				for (IState<S,C> succ2 : succ2s) {
					IState<S, C> succ = getState(succ1, succ2, false);
					m_Result.addInternalTransition(state, symbol, succ);
				}
			}
		}
		
		for (S symbol : state1OnlySymbols) {
			Collection<IState<S,C>> succ1s = state1.getInternalSucc(symbol);
			for (IState<S,C> succ1 : succ1s) {
					IState<S, C> succ = getState(succ1, state2, false);
					m_Result.addInternalTransition(state, symbol, succ);
			}
		}
		
		for (S symbol : state2OnlySymbols) {
			Collection<IState<S,C>> succ2s = state2.getInternalSucc(symbol);
			for (IState<S,C> succ2 : succ2s) {
					IState<S, C> succ = getState(state1, succ2, false);
					m_Result.addInternalTransition(state, symbol, succ);
			}
		}

		
	}

	public void constructInitialStates() {
		for (IState<S,C> state1 : M_Nwa1.getInitialStates()) {
			for (IState<S,C> state2 : M_Nwa2.getInitialStates()) {
				getState(state1, state2, true);
			}
		}
	}
	
	
	public ConcurrentProduct(INestedWordAutomaton<S,C> nwa1,
			INestedWordAutomaton<S,C> nwa2, boolean concurrentPrefixProduct) {
		m_ConcurrentPrefixProduct = concurrentPrefixProduct;
		M_Nwa1 = nwa1;
		M_Nwa2 = nwa2;
		m_ContentFactory = nwa1.getContentFactory();
//FIXME
//		if (m_ContentFactory != nwa2.getContentFactory()) {
//			throw new IllegalArgumentException("Both NWAs have to use" +
//					"same ContentFactory");
//		}
		
		if (!nwa1.getCallAlphabet().isEmpty() ||
				!nwa1.getReturnAlphabet().isEmpty() ||
				!nwa2.getCallAlphabet().isEmpty() ||
				!nwa2.getReturnAlphabet().isEmpty()) {
			s_Logger.warn("Call alphabet and return alphabet are ignored.");
		}
		m_SynchronizationAlphabet = new HashSet<S>(nwa1.getInternalAlphabet());
		m_SynchronizationAlphabet.retainAll(nwa2.getInternalAlphabet());
		Set<S> commonAlphabet = new HashSet<S>(nwa1.getInternalAlphabet());
		commonAlphabet.addAll(nwa2.getInternalAlphabet());
		m_Result = new NestedWordAutomaton<S,C>(commonAlphabet,
									 new HashSet<S>(0),
									 new HashSet<S>(0),
									 m_ContentFactory);
		constructInitialStates();
		while (!m_Worklist.isEmpty()) {
			m_Worklist.dequeuePair();
			IState<S,C> state1 = m_Worklist.getDequeuedPairFst();
			IState<S,C> state2 = m_Worklist.getDequeuedPairSnd();
			constructOutgoingTransitions(state1,state2);
		}
	}

	public INestedWordAutomaton<S,C> getResult() {
		return m_Result;
	}
	

	/**
	 * Maps pairs of states to states. 
	 * @author heizmann@informatik.uni-freiburg.de
	 */
	private class StatePair2StateMap {
		Map<IState<S,C>,Map<IState<S,C>,IState<S,C>>> backingMap =
			new HashMap<IState<S,C>, Map<IState<S,C>,IState<S,C>>>();
		
		public IState<S,C> get(IState<S,C> state1, IState<S,C> state2) {
			Map<IState<S,C>,IState<S,C>> snd2result = backingMap.get(state1);
			if (snd2result == null) {
				return null;
			}
			else {
				return snd2result.get(state2);
			}
		}
		
		public void put(IState<S,C> state1,
						IState<S,C> state2,
						IState<S,C> state) {
			Map<IState<S,C>,IState<S,C>> snd2result = backingMap.get(state1);
			if (snd2result == null) {
				snd2result = new HashMap<IState<S,C>,IState<S,C>>();
				backingMap.put(state1,snd2result);
			}
			snd2result.put(state2,state);
		}
	}

	
	/**
	 * Queue for pairs of states. Pairs are not dequeued in the same order as
	 * inserted. 
	 * @author heizmann@informatik.uni-freiburg.de
	 */
	private class StatePairQueue {
		Map<IState<S,C>,Set<IState<S,C>>> m_Queue =
			new HashMap<IState<S,C>,Set<IState<S,C>>>();
		
		IState<S,C> m_DequeuedPairFst;
		IState<S,C> m_DequeuedPairSnd;
		
		public void enqueue(IState<S,C> state1, IState<S,C> state2) {
			Set<IState<S,C>> secondComponets = m_Queue.get(state1);
			if (secondComponets == null) {
				secondComponets = new HashSet<IState<S,C>>();
				m_Queue.put(state1,secondComponets);
			}
			secondComponets.add(state2);
		}
		
		public void dequeuePair() {
			assert (m_DequeuedPairFst == null && m_DequeuedPairSnd == null) : 
				"Results from last dequeue not yet collected!";
			Iterator<IState<S,C>> it1 = m_Queue.keySet().iterator();
			m_DequeuedPairFst = it1.next();
			assert (m_Queue.get(m_DequeuedPairFst) !=  null);
			Set<IState<S,C>> secondComponets = m_Queue.get(m_DequeuedPairFst);
			assert (secondComponets != null);
			Iterator<IState<S,C>> it2 = secondComponets.iterator();
			m_DequeuedPairSnd = it2.next();
			
			secondComponets.remove(m_DequeuedPairSnd);
			if (secondComponets.isEmpty()) {
				m_Queue.remove(m_DequeuedPairFst);
			}
		}
		
		public IState<S, C> getDequeuedPairFst() {
			assert (m_DequeuedPairFst != null) : "No pair dequeued";
			IState<S,C> result = m_DequeuedPairFst;
			m_DequeuedPairFst = null;
			return result;
		}

		public IState<S, C> getDequeuedPairSnd() {
			assert (m_DequeuedPairSnd != null) : "No pair dequeued";
			IState<S,C> result = m_DequeuedPairSnd;
			m_DequeuedPairSnd = null;
			return result;
		}

		public boolean isEmpty() {
			return m_Queue.isEmpty();
		}
	}

}
