package local.stalin.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.nwalibrary.StateDl;
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
public class StandaloneDifference<S,C> {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final INestedWordAutomaton<S,C> minuend;
	private final INestedWordAutomaton<S,C> subtrahend;
	private final INestedWordAutomaton<S,C> difference;
	
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
	
	/**
	 * Summary states of the resulting automaton that have been visited so far.
	 * If the summary state (<i>caller</i>,<i>present</i>) has been visited,
	 * <i>present</i> is contained in the range of <i>caller</i>.
	 */
	private final Map<IState<S,C>,Set<IState<S,C>>> visited = 
		new HashMap<IState<S,C>, Set<IState<S,C>>>();
	
	/**
	 * Summary states of the resulting automaton that still have to be
	 * processed.
	 */
	private final List<SummaryState<S,C>> worklist = 
		new LinkedList<SummaryState<S,C>>();
	
	
	/**
	 * Pairs of states (q,q') of the resulting automaton such that q' is
	 * reachable from q via a well-matched nested word in which the first
	 * position is a call position and the last position is a return position. 
	 */
	private Map<IState<S,C>,Set<IState<S,C>>> summary = 
		new HashMap<IState<S,C>, Set<IState<S,C>>>();
	
	private final IState<S,C> auxilliaryEmptyStackState;
	
	private final ContentFactory<C> contentFactory;
	

	
	public INestedWordAutomaton<S,C> getDifference() {
		return difference;
	}
	
	
	public StandaloneDifference(
			INestedWordAutomaton<S,C> minuend,
			INestedWordAutomaton<S,C> subtrahend,
			IStateDeterminizer<S,C> stateDeterminizer) {
		contentFactory = minuend.getContentFactory();
		this.minuend = minuend;
		this.subtrahend = subtrahend;
		this.stateDeterminizer = stateDeterminizer;
		difference = new NestedWordAutomaton<S, C>(
				minuend.getInternalAlphabet(),
				minuend.getCallAlphabet(),
				minuend.getReturnAlphabet(),
				minuend.getContentFactory());
		auxilliaryEmptyStackState = new StateDl<S,C>(false,
				contentFactory.createSinkStateContent());
		computeDifference();
	}
	
	
	
	
	
	public boolean wasVisited(IState<S,C> callerState, IState<S,C> state) {
		Set<IState<S,C>> callerStates = visited.get(state);
		if (callerStates == null) {
			return false;
		}
		else {
			return callerStates.contains(callerState);
		}
	}
	
	public void markVisited(IState<S,C> callerState, IState<S,C> state) {
		Set<IState<S,C>> callerStates = visited.get(state);
		if (callerStates == null) {
			callerStates = new HashSet<IState<S,C>>();
			visited.put(state, callerStates);
		}
		callerStates.add(callerState);
	}
	

	public void enqueueAndMark(IState<S,C> callerState, IState<S,C> state) {
		if (!wasVisited(callerState, state)) {
			markVisited(callerState, state);
			SummaryState<S,C> statePair = new SummaryState<S,C>(state,callerState);
			worklist.add(statePair);
		}
	}
	
	
	
	public void addSummary(IState<S,C> summaryPred, IState<S,C> summarySucc) {
		Set<IState<S,C>> summarySuccessors = summary.get(summaryPred);
		if (summarySuccessors == null) {
			summarySuccessors = new HashSet<IState<S,C>>();
			summary.put(summaryPred, summarySuccessors);
		}
		summarySuccessors.add(summarySucc);
	}

	
	/**
	 * Get all states <i>resCaller</i> of the resulting automaton (computed so
	 * far) such that the summary state (<i>resCaller</i>,<i>resPresent</i>) has
	 * been visited so far.
	 */
	private Set<IState<S,C>> getKnownCallerStates(IState<S,C> resPresent) {
		Set<IState<S,C>> callerStates = visited.get(resPresent);
		if (callerStates == null) {
			return new HashSet<IState<S,C>>(0);
		}
		else {
			return callerStates;
		}
	}
	
	
	
	
	
	
	
	
	
	
	
	
	
	

	public void computeDifference() {
		DeterminizedState<S,C> detState = new DeterminizedState<S,C>(contentFactory);
		for (IState<S,C> subtState : subtrahend.getInitialStates()) {
			detState.addPair(auxilliaryEmptyStackState,subtState);
		}		
		for (IState<S,C> minuState : minuend.getInitialStates()) {
			DifferenceState<S,C> macrState = 
				new DifferenceState<S,C>(minuState, detState);
			C content = contentFactory.createContentOnIntersection(
					macrState.minuendState.getContent(), 
					macrState.subtrahendDeterminizedState.getContent());
			IState<S,C> diffState = difference.addState(true,
												macrState.isFinal(), content);
			diff2res.put(macrState,diffState);
			res2diff.put(diffState, macrState);
			enqueueAndMark(auxilliaryEmptyStackState, diffState);
		}
		
		while(!worklist.isEmpty()) {
			SummaryState<S,C> statePair = worklist.remove(0);
//			s_Logger.debug("Processing: "+ statePair);
			processSummaryState(statePair);
			if (summary.containsKey(statePair.presentState)) {
				for (IState<S,C> summarySucc : summary.get(statePair.presentState)) {
					enqueueAndMark(statePair.getCallerState(), summarySucc);
				}
			}
		}
	}
	

	

	/**
	 * Let resSummaryState=(<i>caller</i>,<i>present</i>). Extend the
	 * construction of the resulting automaton at <i>present</i> by outgoing
	 * transitions. To decide if a return transition can be added <i>caller</i>
	 * is taken into account. 
	 */
	private void processSummaryState(SummaryState<S,C> resSummaryState) {
		IState<S,C> resState = resSummaryState.getPresentState();
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
					stateDeterminizer.internalSuccessor(detState, symbol);
			for (IState<S,C> minuSucc : minuState.getInternalSucc(symbol)) {
				DifferenceState<S,C> diffSucc = 
						new DifferenceState<S,C>(minuSucc, detSucc);
				IState<S,C> resSucc = getResState(diffSucc);
				difference.addInternalTransition(resState, symbol, resSucc);
				enqueueAndMark(resSummaryState.getCallerState(),resSucc);
			}
		}
		
		for (S symbol : minuState.getSymbolsCall()) {
			if (!subtrahend.getCallAlphabet().contains(symbol)) {
				continue;
			}
			DeterminizedState<S,C> detSucc = 
					stateDeterminizer.callSuccessor(detState, symbol);
			for (IState<S,C> minuSucc : minuState.getCallSucc(symbol)) {
				DifferenceState<S,C> diffSucc = 
						new DifferenceState<S,C>(minuSucc, detSucc);
				IState<S,C> resSucc = getResState(diffSucc);
				difference.addCallTransition(resState, symbol, resSucc);
				enqueueAndMark(resState, resSucc);
			}
		}

		for (S symbol : minuState.getSymbolsReturn()) {
			if (!subtrahend.getReturnAlphabet().contains(symbol)) {
				continue;
			}
			IState<S,C> resLinPred = resSummaryState.getCallerState();
			if (resLinPred == auxilliaryEmptyStackState) {
				continue;
			}
			DifferenceState<S,C> diffLinPred = res2diff.get(resLinPred);
			IState<S, C> minuLinPred = diffLinPred.getMinuendState();
			DeterminizedState<S,C> detLinPred = 
					diffLinPred.getSubtrahendDeterminizedState();
			
			Collection<IState<S,C>> minuSuccs = 
					minuState.getReturnSucc(minuLinPred, symbol);
//			if (minuSuccs.isEmpty()) continue;
			DeterminizedState<S,C> detSucc = 
				stateDeterminizer.returnSuccessor(detState, detLinPred, symbol);
			for (IState<S,C> minuSucc : minuSuccs) {
				DifferenceState<S,C> diffSucc = 
					new DifferenceState<S,C>(minuSucc, detSucc);
				IState<S,C> resSucc = getResState(diffSucc);
				difference.addReturnTransition(
										resState, resLinPred, symbol, resSucc);
				addSummary(resLinPred, resSucc);
				for (IState<S,C> resLinPredCallerState : 
											getKnownCallerStates(resLinPred)) {
					enqueueAndMark(resLinPredCallerState, resSucc);
				}
			}
		}
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
			IState<S,C> resState = difference.addState(false,
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
	
	



	
	
	private class SummaryState<S,C> {
		private final IState<S,C> callerState;
		private final IState<S,C> presentState;
		private final int hashCode;
		public SummaryState(IState<S,C> presentState, IState<S,C> callerState) {
			this.callerState = callerState;
			this.presentState = presentState;
			this.hashCode = 
				3 * callerState.hashCode() + 5 * presentState.hashCode(); 
		}
		
		public IState<S, C> getCallerState() {
			return callerState;
		}


		public IState<S, C> getPresentState() {
			return presentState;
		}



		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(Object obj) {
			if (obj instanceof SummaryState) {
				SummaryState<S,C> summaryState = (SummaryState<S,C>) obj;
				return presentState.equals(summaryState.presentState) && 
								callerState.equals(summaryState.callerState);
			}
			else {
				return false;
			}
		}
		
		@Override
		public int hashCode() {
			return hashCode;
		}

		@Override
		public String toString() {
			return "CallerState: " + callerState + "  State: "+ presentState;
		}
		
	}
	
	
	

}
