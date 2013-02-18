package local.stalin.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import local.stalin.automata.Activator;
import local.stalin.automata.nwalibrary.DoubleDecker;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.nwalibrary.StateDl;
import local.stalin.core.api.StalinServices;


public abstract class DoubleDeckerGraphBuilder<S,C> {
	
	private static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	
	protected NestedWordAutomaton<S,C> result;

	
	/**
	 * DoubleDeckers of the resulting automaton that have been visited so
	 * far. If the DoubleDecker (<i>down</i>,<i>up</i>) has been visited,
	 * <i>up</i> is contained in the range of <i>down</i>.
	 */
	private final Map<IState<S,C>,Set<IState<S,C>>> visited = 
		new HashMap<IState<S,C>, Set<IState<S,C>>>();

	
	/**
	 * DoubleDeckers of the resulting automaton that still have to be
	 * processed.
	 */
	private final List<DoubleDecker<S,C>> worklist = 
		new LinkedList<DoubleDecker<S,C>>();
	
	
	/**
	 * Pairs of states (q,q') of the resulting automaton such that q' is
	 * reachable from q via a well-matched nested word in which the first
	 * position is a call position and the last position is a return position. 
	 */
	private final Map<IState<S,C>, Map<IState<S,C>,IState<S,C>>> 
		callReturnSummary = 
		new HashMap<IState<S,C>, Map<IState<S,C>,IState<S,C>>>();
	
//	/**
//	 * State that is used as caller state of the initial summary states.
//	 */	
//	protected IState<S,C> auxilliaryEmptyStackState;
	
	/**
	 * The result get minimized iff this is set to true
	 */
	protected boolean minimize = false;
	
	/**
	 * Predecessor DoubleDeckers in the graph. Used only of minimization.
	 */
	protected Map<DoubleDecker<S,C>,Set<DoubleDecker<S,C>>> predecessors =
		new HashMap<DoubleDecker<S,C>,Set<DoubleDecker<S,C>>>();
	
//	protected Collection<IState<S,C>> finalStates = 
//		new LinkedList<IState<S,C>>();

	/**
	 * Return the already computed result.
	 */
	public final INestedWordAutomaton<S,C> getResult() {
		return result;
	}
	
	
	
	/**
	 * True iff the DoubleDecker (<i>down</i>,<i>up</i>) has already
	 * been processed or is in the worklist.
	 */
	private final boolean wasVisited(DoubleDecker<S,C> storyState) {
		Set<IState<S,C>> upState = visited.get(storyState.getUp());
		if (upState == null) {
			return false;
		}
		else {
			return upState.contains(storyState.getDown());
		}
	}
	
	/**
	 * Record that a DoubleDecker (<i>down</i>,<i>up</i>) has already
	 * been processed or is in the worklist.
	 */
	private final void markVisited(DoubleDecker<S,C> doubleDecker) {
		Set<IState<S,C>> downStates = visited.get(doubleDecker.getUp());
		if (downStates == null) {
			downStates = new HashSet<IState<S,C>>();
			visited.put(doubleDecker.getUp(), downStates);
		}
		downStates.add(doubleDecker.getDown());
	}
	
	
	
	/**
	 * Add the DoubleDecker (<i>down</i>,<i>up</i>) to the worklist and
	 * record that it has been added.
	 */
	private final void enqueueAndMark(DoubleDecker<S,C> doubleDecker,
												DoubleDecker<S,C> predecessor) {
		if (minimize) {
			addPredecessor(doubleDecker,predecessor);
		}
		if (!wasVisited(doubleDecker)) {
			markVisited(doubleDecker);
			worklist.add(doubleDecker);
		}
	}
	
	/**
	 * Enqueue to worklist and mark visited all summary successors of the
	 * DoubleDecker (<i>down</i>,<i>up</i>)
	 */
	private final void enqueueAndMarkSummarySuccessors(
					DoubleDecker<S,C> doubleDecker) {
		if (callReturnSummary.containsKey(doubleDecker.getUp())) {
			Map<IState<S,C>, IState<S, C>> summarySucc2returnPred = 
				callReturnSummary.get(doubleDecker.getUp());
			for (IState<S,C> summarySucc : summarySucc2returnPred.keySet()) {
				IState<S,C> returnPred = summarySucc2returnPred.get(summarySucc);
				DoubleDecker<S,C> summarySuccDoubleDecker = 
					new DoubleDecker<S,C>(doubleDecker.getDown(), summarySucc);
				DoubleDecker<S,C> shortcutReturnPred = 
					new DoubleDecker<S, C>(doubleDecker.getUp(), returnPred);
				enqueueAndMark(summarySuccDoubleDecker,shortcutReturnPred);
			}
		}
	}
	
	/**
	 * Record that summarySucc is reachable from summaryPred via a run over a
	 * well-matched NestedWord
	 */
	private final void addSummary(IState<S,C> summaryPred,
							IState<S,C> summarySucc, IState<S,C> returnPred) {
		Map<IState<S,C>, IState<S,C>> summarySuccessors = 
			callReturnSummary.get(summaryPred);
		if (summarySuccessors == null) {
			summarySuccessors = new HashMap<IState<S,C>, IState<S,C>>();
			callReturnSummary.put(summaryPred, summarySuccessors);
		}
		summarySuccessors.put(summarySucc, returnPred);
	}

	
	/**
	 * Get all states <i>down</i> such that the DoubleDecker
	 * (<i>down</i>,<i>up</i>) has been visited so far.
	 */
	private final Set<IState<S,C>> getKnownDownStates(IState<S,C> current) {
		Set<IState<S,C>> downStates = visited.get(current);
		if (downStates == null) {
			return new HashSet<IState<S,C>>(0);
		}
		else {
			return downStates;
		}
	}
	
	protected final void computeResult() {
		Collection<IState<S,C>> initialStates = computeInitialStates();
		for (IState<S,C> state : initialStates) {
			DoubleDecker<S,C> doubleDecker = 
				new DoubleDecker<S,C>(result.getEmptyStackState(), state);
			enqueueAndMark(doubleDecker,null);
		}
		
		while(!worklist.isEmpty()) {
			DoubleDecker<S,C> doubleDecker = worklist.remove(0);
//			s_Logger.debug("Processing: "+ statePair);
			Collection<IState<S,C>> internalSuccs = 
					computeInternalSuccessors(doubleDecker);
			for (IState<S,C> succ : internalSuccs) {
				DoubleDecker<S,C> succDoubleDecker = 
					new DoubleDecker<S,C>(doubleDecker.getDown(), succ);
				enqueueAndMark(succDoubleDecker,doubleDecker);
				enqueueAndMarkSummarySuccessors(succDoubleDecker);

			}
			Collection<IState<S,C>> callSuccs = 
				computeCallSuccessors(doubleDecker);
			for (IState<S,C> succ : callSuccs) {
				DoubleDecker<S,C> succDoubleDecker = 
					new DoubleDecker<S,C>(doubleDecker.getUp(), succ);
				enqueueAndMark(succDoubleDecker,doubleDecker);
				enqueueAndMarkSummarySuccessors(succDoubleDecker);
			}
			Collection<IState<S,C>> returnSuccs = 
				computeReturnSuccessors(doubleDecker);
			for (IState<S,C> succ : returnSuccs) {
				addSummary(doubleDecker.getDown(), succ,doubleDecker.getUp());
				for (IState<S,C> resLinPredCallerState : 
					getKnownDownStates(doubleDecker.getDown())) {
					DoubleDecker<S,C> succDoubleDecker = 
						new DoubleDecker<S,C>(resLinPredCallerState, succ);
					enqueueAndMark(succDoubleDecker,doubleDecker);
					enqueueAndMarkSummarySuccessors(succDoubleDecker);
				}
			}
		}
		s_Logger.info("Result " + result.sizeInformation());
		if (minimize) {
			removeStatesThatCanNotReachFinal();
		}
		s_Logger.info("Minimized result " + result.sizeInformation());
	}

	
	protected abstract Collection<IState<S,C>> computeInitialStates();

	protected abstract Collection<IState<S,C>> computeInternalSuccessors(
			DoubleDecker<S,C> state);

	protected abstract Collection<IState<S,C>> computeCallSuccessors(
			DoubleDecker<S,C> state);

	protected abstract Collection<IState<S,C>> computeReturnSuccessors(
			DoubleDecker<S,C> state);
	
	private final void addPredecessor(DoubleDecker<S,C> doubleDecker, 
									DoubleDecker<S,C> predecessorDoubleDecker) {
		if (predecessorDoubleDecker != null) {
			Set<DoubleDecker<S,C>> predSet = predecessors.get(doubleDecker);
			if (predSet == null) {
				predSet = new HashSet<DoubleDecker<S,C>>();
				predecessors.put(doubleDecker, predSet);
			}
			predSet.add(predecessorDoubleDecker);
		}
	}
	
	
	
	private final void removeStatesThatCanNotReachFinal() {
		// DoubleDeckers that have been visited in this search which starts from
		// final states
		HashSet<DoubleDecker<S,C>> visitedDoubleDeckers = 
			new HashSet<DoubleDecker<S,C>>();
		// Queue of this search which starts from final states
		LinkedList<DoubleDecker<S, C>> reverseSearchWorklist = 
			new LinkedList<DoubleDecker<S,C>>();
		// Set used to compute the states that can never reach the final state
		// initialized with all states and narrowed by the algorithm
		HashSet<IState<S,C>> statesNeverReachFinal = 
			new HashSet<IState<S,C>>(result.getAllStates());
		
		for (IState<S,C> finalState : result.getFinalStates()) {
			for (IState<S,C> downStatesOfFinal : visited.get(finalState)) {
				DoubleDecker<S,C> summary =
					new DoubleDecker<S,C>(downStatesOfFinal, finalState);
				visitedDoubleDeckers.add(summary);
				statesNeverReachFinal.remove(summary.getUp());
				reverseSearchWorklist.add(summary);
			}
		}
		while (!reverseSearchWorklist.isEmpty()) {
			DoubleDecker<S,C> doubleDecker= reverseSearchWorklist.removeFirst();
			Set<DoubleDecker<S,C>> preds = predecessors.get(doubleDecker);
			statesNeverReachFinal.remove(doubleDecker.getUp());
			if (preds == null) {
				assert result.getInitialStates().contains(doubleDecker.getUp());
			}
			else {
				for (DoubleDecker<S,C> pred : predecessors.get(doubleDecker)) {
					if (!visitedDoubleDeckers.contains(pred)) {
						visitedDoubleDeckers.add(pred);
						reverseSearchWorklist.add(pred);
					}
				}
			}
		}
		for (IState<S,C> state : statesNeverReachFinal) {
			StateDl<S,C> stateDl = (StateDl<S, C>) state;
			stateDl.removeState(stateDl,result);
		}
		assert ((NestedWordAutomaton<S,C>)result).allStatesRegistered();
	}



	
	

	
	
}
