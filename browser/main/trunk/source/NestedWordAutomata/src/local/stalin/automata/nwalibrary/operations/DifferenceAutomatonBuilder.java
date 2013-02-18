package local.stalin.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.DoubleDecker;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.core.api.StalinServices;
import org.apache.log4j.Logger;



/**
 * Given two nondeterministic NWAs nwa_minuend and nwa_subtrahend a
 * DifferenceAutomatonBuilder can compute a NWA nwa_difference
 * such that nwa_difference accepts all words that are accepted by nwa_minuend
 * but not by Psi(nwa_subtrahend), i.e. 
 * L(nwa_difference) = L(nwa_minuend) \ L( Psi(nwa_subtrahend) ),
 * where Psi is a transformation of the automaton nwa_subtrahend that is defined
 * by an implementation of IStateDeterminizer.
 * 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Symbol. Type of the elements of the alphabet over which the
 * automata are defined. 
 * @param <C> Content. Type of the labels that are assigned to the states of
 * automata. In many cases you want to use String as C and your states are
 * labeled e.g. with "q0", "q1", ... 
 */
//TODO: Optimization for special case where subtrahend is closed under
// concatenation with Sigma^*. Use only one DeterminizedState detFin state that
// represents all final states. Each successor of detFin is detFin itself.
public class DifferenceAutomatonBuilder<S,C> 
		extends DoubleDeckerGraphBuilder<S, C> {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final INestedWordAutomaton<S,C> minuend;
	private final INestedWordAutomaton<S,C> subtrahend;
	
	private final IState<S,C> subtrahendAuxilliaryEmptyStackState;
	
	private final IStateDeterminizer<S,C> stateDeterminizer;
	
	/**
	 * Maps a DifferenceState to its representative in the resulting automaton.
	 */
	private Map<DifferenceState<S,C>,IState<S,C>> diff2res =
		new HashMap<DifferenceState<S,C>, IState<S,C>>();
	
	/**
	 * Maps a state in resulting automaton to the DifferenceState for which it
	 * was created.
	 */
	private final Map<IState<S,C>,DifferenceState<S,C>> res2diff =
		new HashMap<IState<S,C>, DifferenceState<S,C>>();
	
	private final ContentFactory<C> contentFactory;
	
	
	private INestedWordAutomaton<S,DeterminizedState<S,C>> 
													m_DeterminizedSubtrahend;

	
	
	int m_InternalSuccs = 0;
	int m_InternalSuccsCache = 0;
	int m_CallSuccs = 0;
	int m_CallSuccsCache = 0;
	int m_ReturnSuccs = 0;
	int m_ReturnSuccsCache = 0;
	int m_Unnecessary = 0;
	
	
	Map<DeterminizedState,DeterminizedState> m_DetStateCache =
		new HashMap<DeterminizedState,DeterminizedState>();
	
	Map<DeterminizedState,Map<S,DeterminizedState>>	m_InternalSuccessorCache =
	new HashMap<DeterminizedState,Map<S,DeterminizedState>>();
	
	Map<DeterminizedState,Map<S,DeterminizedState>>	m_CallSuccessorCache =
		new HashMap<DeterminizedState,Map<S,DeterminizedState>>();
	
	Map<DeterminizedState,Map<DeterminizedState,Map<S,DeterminizedState>>> 
	 m_ReturnSuccessorCache = new HashMap<DeterminizedState,
		Map<DeterminizedState,Map<S,DeterminizedState>>>();
	
	
	
	private DeterminizedState internalSuccessorCache(
			DeterminizedState  state,
			S symbol) {
		Map<S, DeterminizedState> symbol2succ = 
			m_InternalSuccessorCache.get(state);
		if (symbol2succ == null) {
			return null;
		}
		return symbol2succ.get(symbol);
	}
	
	private void putInternalSuccessorCache(
			DeterminizedState  state,
			S symbol,
			DeterminizedState  succ) {
		Map<S, DeterminizedState> symbol2succ = 
			m_InternalSuccessorCache.get(state);
		if (symbol2succ == null) {
			symbol2succ = new HashMap<S,DeterminizedState>();
			m_InternalSuccessorCache.put(state, symbol2succ);
		}
		symbol2succ.put(symbol, succ);	
	}
	
	
	
	private DeterminizedState callSuccessorCache(
			DeterminizedState  state,
			S symbol) {
		Map<S, DeterminizedState> symbol2succ = 
			m_CallSuccessorCache.get(state);
		if (symbol2succ == null) {
			return null;
		}
		return symbol2succ.get(symbol);
	}
	
	private void putCallSuccessorCache(
			DeterminizedState  state,
			S symbol,
			DeterminizedState  succ) {
		Map<S, DeterminizedState> symbol2succ = 
			m_CallSuccessorCache.get(state);
		if (symbol2succ == null) {
			symbol2succ = new HashMap<S,DeterminizedState>();
			m_CallSuccessorCache.put(state, symbol2succ);
		}
		symbol2succ.put(symbol, succ);	
	}
	
	private DeterminizedState returnSuccessorCache(
			DeterminizedState  state,
			DeterminizedState linPred,
			S symbol) {
		Map<DeterminizedState,Map<S, DeterminizedState>> linPred2symbol2succ =
			m_ReturnSuccessorCache.get(linPred);
		if (linPred2symbol2succ == null) {
			return null;
		}
		Map<S, DeterminizedState> symbol2succ = 
			linPred2symbol2succ.get(state);
		if (symbol2succ == null) {
			return null;
		}
		return symbol2succ.get(symbol);
	}
	
	private void putReturnSuccessorCache(
			DeterminizedState  state,
			DeterminizedState linPred,
			S symbol,
			DeterminizedState  succ) {
		Map<DeterminizedState,Map<S, DeterminizedState>> linPred2symbol2succ =
			m_ReturnSuccessorCache.get(linPred);
		if (linPred2symbol2succ == null) {
			linPred2symbol2succ = 
				new HashMap<DeterminizedState,Map<S, DeterminizedState>>();
			m_ReturnSuccessorCache.put(linPred, linPred2symbol2succ);
		}
		Map<S, DeterminizedState> symbol2succ = 
			linPred2symbol2succ.get(state);
		if (symbol2succ == null) {
			symbol2succ = new HashMap<S,DeterminizedState>();
			linPred2symbol2succ.put(state, symbol2succ);
		}
		symbol2succ.put(symbol, succ);	
	}
	
	
	
	
	
	public DifferenceAutomatonBuilder(
			INestedWordAutomaton<S,C> minuend,
			INestedWordAutomaton<S,C> subtrahend,
			IStateDeterminizer<S,C> stateDeterminizer,
			boolean minimize) {
		s_Logger.debug("Start constuction of difference. Minuend has " + 
				minuend.getAllStates().size() + " states. Subtrahend has " + 
				subtrahend.getAllStates().size() + " states.");
		contentFactory = minuend.getContentFactory();
		this.minuend = minuend;
		this.subtrahend = subtrahend;
		this.subtrahendAuxilliaryEmptyStackState = 
			((NestedWordAutomaton<S,C>)subtrahend).getEmptyStackState();
		this.stateDeterminizer = stateDeterminizer;
		super.result = new NestedWordAutomaton<S,C>(
				minuend.getInternalAlphabet(),
				minuend.getCallAlphabet(),
				minuend.getReturnAlphabet(),
				minuend.getContentFactory());
		super.minimize = minimize;
		
		m_DeterminizedSubtrahend = 
			new NestedWordAutomaton<S,DeterminizedState<S,C>>(
					minuend.getInternalAlphabet(), 
					minuend.getCallAlphabet(), 
					minuend.getReturnAlphabet(), 
					null);
		computeResult();
		s_Logger.debug("Finished construction of difference. Result has " 
				+ result.getAllStates().size() + " states.");
		s_Logger.info("Computed internal successors:" + m_InternalSuccs);
		s_Logger.info("Internal successors via cache:" + m_InternalSuccsCache);
		s_Logger.info("Computed call successors:" + m_CallSuccs);
		s_Logger.info("Call successors via cache:" + m_CallSuccsCache);
		s_Logger.info("Computed return successors:" + m_ReturnSuccs);
		s_Logger.info("Return successors via cache:" + m_ReturnSuccsCache);
		s_Logger.info("You can save " + m_Unnecessary + " successor" +
				" computations if you exploit sigma star concat closure");
	}
	
	public DifferenceAutomatonBuilder(
			INestedWordAutomaton<S,C> minuend,
			INestedWordAutomaton<S,C> subtrahend) {
		s_Logger.debug("Start constuction of difference. Minuend has " + 
				minuend.getAllStates().size() + " states. Subtrahend has " + 
				subtrahend.getAllStates().size() + " states.");
		contentFactory = minuend.getContentFactory();
		this.minuend = minuend;
		this.subtrahend = subtrahend;
		this.subtrahendAuxilliaryEmptyStackState = 
			((NestedWordAutomaton<S,C>)subtrahend).getEmptyStackState();
		this.stateDeterminizer =
			new PowersetSuccessorStateDeterminization<S,C>(contentFactory);
		super.result = new NestedWordAutomaton<S,C>(
				minuend.getInternalAlphabet(),
				minuend.getCallAlphabet(),
				minuend.getReturnAlphabet(),
				minuend.getContentFactory());
		super.minimize = false;
		
		m_DeterminizedSubtrahend = 
			new NestedWordAutomaton<S,DeterminizedState<S,C>>(
					minuend.getInternalAlphabet(), 
					minuend.getCallAlphabet(), 
					minuend.getReturnAlphabet(), 
					null);
		computeResult();
		s_Logger.debug("Finished construction of difference. Result has " 
				+ result.getAllStates().size() + " states.");
	}

	
	
	
	
	
	

	@Override
	protected Collection<IState<S, C>> computeInitialStates() {
		ArrayList<IState<S, C>> resInitials = 
			new ArrayList<IState<S,C>>(subtrahend.getInitialStates().size());
		DeterminizedState<S,C> detState = 
			new DeterminizedState<S,C>(contentFactory);
		for (IState<S,C> subtState : subtrahend.getInitialStates()) {
			detState.addPair(subtrahendAuxilliaryEmptyStackState,subtState);
		}
		m_DetStateCache.put(detState, detState);
		for (IState<S,C> minuState : minuend.getInitialStates()) {
			DifferenceState<S,C> diffState = 
				new DifferenceState<S,C>(minuState, detState);
			C content = contentFactory.createContentOnIntersection(
					diffState.minuendState.getContent(), 
					diffState.subtrahendDeterminizedState.getContent());
			IState<S,C> resState = result.addState(true,
												diffState.isFinal(), content);
			diff2res.put(diffState,resState);
			res2diff.put(resState, diffState);
			resInitials.add(resState);
		}
		return resInitials;
	}


	
	@Override
	protected Collection<IState<S, C>> computeInternalSuccessors(
											DoubleDecker<S,C> doubleDecker) {
		List<IState<S,C>> resInternalSuccessors = new LinkedList<IState<S,C>>();
		IState<S,C> resState = doubleDecker.getUp();
		DifferenceState<S,C> diffState = res2diff.get(resState);
		IState<S,C> minuState = 
			diffState.getMinuendState();
		DeterminizedState<S,C> detState = 
			diffState.getSubtrahendDeterminizedState();
				
		for (S symbol : minuState.getSymbolsInternal()) {
			if (!subtrahend.getInternalAlphabet().contains(symbol)) {
				continue;
			}
			DeterminizedState<S,C> detSucc = 
									internalSuccessorCache(detState, symbol);
			if (detState.isFinal()) m_Unnecessary++; 
			if (detSucc == null) {
				m_InternalSuccs++;
				detSucc = stateDeterminizer.internalSuccessor(detState, symbol);
				if (m_DetStateCache.containsKey(detSucc)) {
					detSucc = m_DetStateCache.get(detSucc);
				}
				else {
					m_DetStateCache.put(detSucc, detSucc);
				}
				putInternalSuccessorCache(detState, symbol, detSucc);
			}
			else {
				m_InternalSuccsCache++;
			}	
			for (IState<S,C> minuSucc : minuState.getInternalSucc(symbol)) {
				DifferenceState<S,C> diffSucc = 
						new DifferenceState<S,C>(minuSucc, detSucc);
				IState<S,C> resSucc = getResState(diffSucc);
				result.addInternalTransition(resState, symbol, resSucc);
				resInternalSuccessors.add(resSucc);
			}
		}
		return resInternalSuccessors;
	}







	@Override
	protected Collection<IState<S,C>> computeCallSuccessors(
			DoubleDecker<S, C> doubleDecker) {
		List<IState<S,C>> resCallSuccessors = new LinkedList<IState<S,C>>();
		IState<S,C> resState = doubleDecker.getUp();
		DifferenceState<S,C> diffState = res2diff.get(resState);
		IState<S,C> minuState = 
			diffState.getMinuendState();
		DeterminizedState<S,C> detState = 
			diffState.getSubtrahendDeterminizedState(); 
		
		for (S symbol : minuState.getSymbolsCall()) {
			if (!subtrahend.getCallAlphabet().contains(symbol)) {
				continue;
			}
			DeterminizedState<S,C> detSucc = 
									callSuccessorCache(detState, symbol);
			if (detState.isFinal()) m_Unnecessary++;
			if (detSucc == null) {
				m_CallSuccs++;
				detSucc = stateDeterminizer.callSuccessor(detState, symbol);
				if (m_DetStateCache.containsKey(detSucc)) {
					detSucc = m_DetStateCache.get(detSucc);
				}
				else {
					m_DetStateCache.put(detSucc, detSucc);
				}
				putCallSuccessorCache(detState, symbol, detSucc);
			}
			else {
				m_CallSuccsCache++;
			}
			for (IState<S,C> minuSucc : minuState.getCallSucc(symbol)) {
				DifferenceState<S,C> diffSucc = 
						new DifferenceState<S,C>(minuSucc, detSucc);
				IState<S,C> resSucc = getResState(diffSucc);
				result.addCallTransition(resState, symbol, resSucc);
				resCallSuccessors.add(resSucc);
			}
		}
		return resCallSuccessors;
	}









	@Override
	protected Collection<IState<S,C>> computeReturnSuccessors(
			DoubleDecker<S,C> doubleDecker) {
		List<IState<S,C>> resReturnSuccessors = new LinkedList<IState<S,C>>();
		IState<S,C> resState = doubleDecker.getUp();
		DifferenceState<S,C> diffState = res2diff.get(resState);
		IState<S,C> minuState = 
			diffState.getMinuendState();
		DeterminizedState<S,C> detState = 
			diffState.getSubtrahendDeterminizedState(); 
		
		IState<S,C> resLinPred = doubleDecker.getDown();
		if (resLinPred == result.getEmptyStackState()) {
			return resReturnSuccessors;
		}
		

		
		DifferenceState<S,C> diffLinPred = res2diff.get(resLinPred);
		IState<S, C> minuLinPred = diffLinPred.getMinuendState();
		
		DeterminizedState<S,C> detLinPred = 
			diffLinPred.getSubtrahendDeterminizedState();
		
		for (S symbol : minuState.getSymbolsReturn()) {
			
			Collection<IState<S,C>> minuSuccs = 
				minuState.getReturnSucc(minuLinPred, symbol);
			// do nothing if there will be no successor difference state
			if (minuSuccs.isEmpty()) continue;
			
			if (!subtrahend.getReturnAlphabet().contains(symbol)) continue;
			
			DeterminizedState<S,C> detSucc = 
							returnSuccessorCache(detState, detLinPred, symbol);
			if (detState.isFinal()) m_Unnecessary++;
			if (detSucc == null) {
				m_ReturnSuccs++;
				detSucc = stateDeterminizer.returnSuccessor(
												detState, detLinPred, symbol);
//				s_Logger.debug("Successor of state " + detState + " symbol " +
//						symbol + " linPred " + detLinPred + " is " + detSucc);
				
				if (m_DetStateCache.containsKey(detSucc)) {
					detSucc = m_DetStateCache.get(detSucc);
				}
				else {
					m_DetStateCache.put(detSucc, detSucc);
				}
				putReturnSuccessorCache(detState, detLinPred, symbol, detSucc);
			}
			else {
				m_ReturnSuccsCache++;
			}			
			
			for (IState<S,C> minuSucc : minuSuccs) {
				DifferenceState<S,C> diffSucc = 
					new DifferenceState<S,C>(minuSucc, detSucc);
				IState<S,C> resSucc = getResState(diffSucc);
				result.addReturnTransition(
										resState, resLinPred, symbol, resSucc);
				resReturnSuccessors.add(resSucc);
			}
		}
		return resReturnSuccessors;
	}




	
	
	/**
	 * Get the state in the resulting automaton that represents a
	 * DifferenceState. If this state in the resulting automaton does not exist
	 * yet, construct it.
	 */
	IState<S,C> getResState(DifferenceState<S,C> diffState) {
		if (diff2res.containsKey(diffState)) {
			return diff2res.get(diffState);
		}
		else {
			C content = contentFactory.createContentOnIntersection(
					diffState.minuendState.getContent(), 
					diffState.subtrahendDeterminizedState.getContent());
			IState<S,C> resState = result.addState(false,
												diffState.isFinal(), content);
			diff2res.put(diffState,resState);
			res2diff.put(resState,diffState);
			return resState;
		}
	}
	
	





/**
 * State of an NWA that accepts the language difference of two NWAs.
 * A DifferenceState is a pair whose first entry is a state of the minuend, the
 * second entry is a DeterminizedState of the subtrahend. A DifferenceState is
 * final iff the minuend state is final and the subtrahend state is not final. 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Symbol
 * @param <C> Content
 */
	private class DifferenceState<S,C> {
		final IState<S,C> minuendState;
		final DeterminizedState<S,C> subtrahendDeterminizedState;
		final boolean isFinal;
		final int m_hashCode; 
		
		
		public DifferenceState(	
				IState<S,C> minuendState, 
				DeterminizedState<S,C> subtrahendDeterminizedState) {
			
			this.minuendState = minuendState;
			this.subtrahendDeterminizedState = subtrahendDeterminizedState;
			this.isFinal = minuendState.isFinal() &&
										!subtrahendDeterminizedState.isFinal();
			m_hashCode = 3 * minuendState.hashCode() +
									5 * subtrahendDeterminizedState.hashCode();
			//FIXME: hasCode of StatePairList may change over time!
		}
		
		public IState<S, C> getMinuendState() {
			return minuendState;
		}

		public DeterminizedState<S, C> getSubtrahendDeterminizedState() {
			return subtrahendDeterminizedState;
		}

		public boolean isFinal() {
			return this.isFinal;
		}
		
		/**
		 * Two DifferenceStates are equivalent iff each, their minuend states
		 * and their subtrahend states are equivalent.
		 */
		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(Object obj) {
			if (obj instanceof DifferenceState) {
				DifferenceState<S,C> diffState = (DifferenceState<S,C>) obj;
				return diffState.minuendState == this.minuendState
					&& this.subtrahendDeterminizedState.equals(
										diffState.subtrahendDeterminizedState);
			}
			else {
				return false;
			}
		}

		@Override
		public int hashCode() {
			return m_hashCode;
		}
		
		@Override
		public String toString() {
			return "<[< " + minuendState.toString() + " , "
					+ subtrahendDeterminizedState.toString() + ">]>";
		}	
	}

	
}
