package local.stalin.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.apache.log4j.Logger;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.CompareByHash;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.core.api.StalinServices;


/**
 * Implementation of Intersection. Result contains only states that are
 * connected to an initial state in the graph representation of the product
 * automaton. Some of this states may not be reachable because runs may not
 * satisfy the stack discipline.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class Intersection<S,C> {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private INestedWordAutomaton<S, C> nwa1;

	public Intersection (INestedWordAutomaton<S,C> nwa) {
		this.nwa1 = nwa;
	}
	
	/**
	 * Maps a pair of states (s1,s2) to the product state ps that represents
	 * the pair.
	 */
	Map<IState<S,C>,Map<IState<S,C>,IState<S,C>>> m_pair2ps = 
				new HashMap<IState<S,C>, Map<IState<S,C>, IState<S,C>>>();
	/**
	 * Maps a product state ps=(s1,s2) to its first component.
	 */
	Map<IState<S,C>,IState<S,C>> m_psTos1 = 
				new HashMap<IState<S,C>,IState<S,C>>();
	/**
	 * Maps a product state ps=(s1,s2) to its second component.
	 */
	Map<IState<S,C>,IState<S,C>> m_psTos2 = 
				new HashMap<IState<S,C>,IState<S,C>>();
	
	Map<IState<S,C>,Map<IState<S,C>,Set<ReturnTransition>>> m_ReturnTransitionQueue =
				new HashMap<IState<S,C>,Map<IState<S,C>,Set<ReturnTransition>>>();
	
	LinkedList<IState<S,C>> m_toprocess = new LinkedList<IState<S,C>>();
	Set<IState<S,C>> m_visited = new HashSet<IState<S,C>>();
	
	INestedWordAutomaton<S,C> m_nwa2;
	NestedWordAutomaton<S,C> m_result;
	
	public INestedWordAutomaton<S,C> buildProduct(INestedWordAutomaton<S,C> nwa2) {
		m_nwa2 = nwa2;
		// Intersect alphabets
		//FIXME: Case where Symbol is compareable
		Set<S> newInternals = new TreeSet<S>(CompareByHash.instance);
		newInternals.addAll(nwa1.getInternalAlphabet());
		newInternals.retainAll(nwa2.getInternalAlphabet());
		Set<S> newCalls = new TreeSet<S>(CompareByHash.instance);
		newCalls.addAll(nwa1.getCallAlphabet());
		newCalls.retainAll(nwa2.getCallAlphabet());
		Set<S> newReturns = new TreeSet<S>(CompareByHash.instance);
		newReturns.addAll(nwa1.getReturnAlphabet());
		newReturns.retainAll(nwa2.getReturnAlphabet());
		
		
		m_result = new NestedWordAutomaton<S,C>(newInternals, newCalls, newReturns, nwa1.getContentFactory());
		for (IState<S,C> fst : nwa1.getInitialStates()) {
			for (IState<S,C> snd : m_nwa2.getInitialStates()) {
				IState<S,C> ps = getProductState(fst, snd);
				m_toprocess.add(ps);
				m_visited.add(ps);
			}
		}
		
		
		while (!m_toprocess.isEmpty()) {
			IState<S,C> ps = m_toprocess.removeFirst();
			IState<S,C> fst = m_psTos1.get(ps);
			IState<S,C> snd = m_psTos2.get(ps);
			for (S symbol : fst.getSymbolsInternal()) {
				Collection<IState<S,C>> succSet1 = fst.getInternalSucc(symbol);
				Collection<IState<S,C>> succSet2 = snd.getInternalSucc(symbol);
				addInternalTransition(ps, symbol, succSet1, succSet2);
			}
			for (S symbol : fst.getSymbolsCall()) {
				Collection<IState<S,C>> succSet1 = fst.getCallSucc(symbol);
				Collection<IState<S,C>> succSet2 = snd.getCallSucc(symbol);
				addCallTransition(ps, symbol, succSet1, succSet2);
			}
			for (S symbol : fst.getSymbolsReturn()) {
				Collection<IState<S,C>> linPredSet1 = fst.getReturnLinearPred(symbol); 
				Collection<IState<S,C>> linPredSet2 = snd.getReturnLinearPred(symbol);
				addReturns(ps, fst, snd, symbol, linPredSet1, linPredSet2);
			}
		}
		s_Logger.debug("Processing at least "+m_ReturnTransitionQueue.size()+ " return transitions.");
		for (IState<S,C> s1linPred : m_ReturnTransitionQueue.keySet()) {
			Map<IState<S, C>, IState<S, C>> s2linPred2ps = m_pair2ps.get(s1linPred);
			if (s2linPred2ps != null) {
				for (IState<S,C> s2linPred : m_ReturnTransitionQueue.get(s1linPred).keySet()) {
					IState<S, C> plinPred = s2linPred2ps.get(s2linPred);
					if (plinPred != null) {
						for (ReturnTransition retTrans : m_ReturnTransitionQueue.get(s1linPred).get(s2linPred)) {
							m_result.addReturnTransition(retTrans.getPred(), plinPred, retTrans.getSymbol(), retTrans.getSucc());
						}
					}
				}
			}
		}
		
		return m_result;
	}

	private IState<S,C> getProductState(IState<S,C> s1, IState<S,C> s2) {
		Map<IState<S,C>, IState<S,C>> s2ToPs;
		if (m_pair2ps.containsKey(s1)) {
			s2ToPs = m_pair2ps.get(s1);
			if (s2ToPs.containsKey(s2)) {
				return s2ToPs.get(s2);
			}
		}
		else {
			s2ToPs = new HashMap<IState<S,C>, IState<S,C>>();
			m_pair2ps.put(s1, s2ToPs);
		}
		C newContent = nwa1.getContentFactory().createContentOnIntersection(s1.getContent(), s2.getContent());
		boolean isFinal = s1.isFinal() && s2.isFinal();
		boolean isInitial = nwa1.getInitialStates().contains(s1) && m_nwa2.getInitialStates().contains(s2);
		IState<S,C> newState = m_result.addState(isInitial, isFinal, newContent);
		s2ToPs.put(s2,newState);
		m_psTos1.put(newState, s1);
		m_psTos2.put(newState, s2);
		return newState;			
	}
	
	
	private void addInternalTransition(IState<S,C> state,S symbol,
								   Collection<IState<S,C>> succSet1,
								   Collection<IState<S,C>> succSet2) {
		assert (succSet1 != null);
		if (succSet2 == null) {
			return;
		}
		for (IState<S,C> s1 : succSet1) {
			for (IState<S,C> s2 : succSet2) {
				IState<S,C> ps = getProductState(s1, s2);
				m_result.addInternalTransition(state, symbol, ps);
				if (!m_visited.contains(ps)) {
					m_visited.add(ps);
					m_toprocess.add(ps);
				}
			}
		}
	}
	
	private void addCallTransition(IState<S,C> state,
								S symbol,
							   Collection<IState<S,C>> succSet1,
							   Collection<IState<S,C>> succSet2) {
		assert (succSet1 != null);
		if (succSet2 == null) {
			return;
		}
		for (IState<S,C> s1 : succSet1) {
			for (IState<S,C> s2 : succSet2) {
				IState<S,C> ps = getProductState(s1, s2);
				m_result.addCallTransition(state, symbol, ps);
				if (!m_visited.contains(ps)) {
					m_visited.add(ps);
					m_toprocess.add(ps);
				}
			}
		}
	}

	
	private void addReturns(IState<S,C> ps, 
							IState<S,C> fst,IState<S, C> snd, 
							S symbol,
							Collection<IState<S, C>> linPredSet1,
							Collection<IState<S, C>> linPredSet2) {
		assert (linPredSet1 != null);
		if (linPredSet2 == null) {
			return;
		}
		for (IState<S,C> s1linPred : linPredSet1) {
			for (IState<S,C> s2linPred : linPredSet2) {
//				IState<S,C> psLinPred = getProductState(s1linPred, s2linPred);
				Collection<IState<S,C>> succSet1 = fst.getReturnSucc(s1linPred, symbol);
				Collection<IState<S,C>> succSet2 = snd.getReturnSucc(s2linPred, symbol);
				addReturnTransitionIfNecessary(ps, s1linPred, s2linPred, symbol, succSet1, succSet2);
				}
			}
		}

	private void addReturnTransitionIfNecessary(IState<S, C> ps,
									 IState<S, C> s1linPred,
									 IState<S, C> s2linPred,
									 S symbol,
									 Collection<IState<S, C>> succSet1,
									 Collection<IState<S, C>> succSet2) {
		for (IState<S,C> s1 : succSet1) {
			for (IState<S,C> s2 : succSet2) {
				IState<S,C> psSucc = getProductState(s1, s2);
				enqueueReturnTransition(s1linPred,s2linPred, new ReturnTransition(ps,symbol,psSucc));
//				m_result.addReturnTransition(ps, psLinPred,symbol, psSucc);
				if (!m_visited.contains(psSucc)) {
					m_visited.add(ps);
					m_toprocess.add(psSucc);
				}
			}
		}
	}
	
	private void enqueueReturnTransition(IState<S, C> s1linPred,
			IState<S, C> s2linPred, ReturnTransition returnTransition) {
		Map<IState<S, C>, Set<ReturnTransition>> s2linPredToReturnTransition = m_ReturnTransitionQueue.get(s1linPred);
		if (s2linPredToReturnTransition == null) {
			s2linPredToReturnTransition = new HashMap<IState<S, C>, Set<ReturnTransition>>();
			m_ReturnTransitionQueue.put(s1linPred, s2linPredToReturnTransition);
		}
		Set<ReturnTransition> returnTransitions = s2linPredToReturnTransition.get(s2linPred);
		if (returnTransitions == null) {
			returnTransitions = new HashSet<ReturnTransition>();
			s2linPredToReturnTransition.put(s2linPred, returnTransitions);
		}
		returnTransitions.add(returnTransition);
	}

	private class ReturnTransition {
		private final IState<S,C> pred;
		private final S symbol;
		private final IState<S,C> succ;
		
		public ReturnTransition(IState<S, C> pred, S symbol,
				IState<S, C> succ) {
			this.pred = pred;
			this.symbol = symbol;
			this.succ = succ;
		}
		/**
		 * @return the pred
		 */
		public IState<S, C> getPred() {
			return pred;
		}
		/**
		 * @return the symbol
		 */
		public S getSymbol() {
			return symbol;
		}
		/**
		 * @return the succ
		 */
		public IState<S, C> getSucc() {
			return succ;
		}
		

	}
}