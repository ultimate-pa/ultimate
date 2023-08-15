package de.uni_freiburg.informatik.ultimate.automata.dynamic_stratified_reduction;

import java.util.ArrayDeque;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DepthFirstTraversal;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.abstraction.IndependenceRelationWithAbstraction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.util.DfsBookkeeping;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Quad;



/**
 *  Implementation of the sleep set automaton using dynamically computed stratified independence relations.
 * Its basically a depth first traversal over the reduction automaton, during which the automaton is being built.
 * 
 *  
 * @param <L>
 *            The type of letters of the input automaton. VariableAbstraction says that they need to be IActions?
 * @param <S>
 *            The type of states of the input automaton.
 * 
 * 
 * - gibt an, welche übergänge da sind
 * - gibt an, welches abstraktionslevel deren target states haben?
 * 
 * instead of constructing a new automaton modify the input automaton?
 * 
 * possible outcomes: 
 * 1) find accepting state  -> example trace for next refinement round
 * 2) fully traverse/build automaton without constructing an accepting state  -> program is correct
 * 
 * 		what do we need to return in those cases?
 */


public class DynamicStratifiedReduction<L, S> {
	private static final String ABORT_MSG = "visitor aborted traversal";

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOriginalAutomaton;
	private NestedWordAutomaton<L, StratifiedReductionState<L,S>> mReductionAutomaton;
	private StratifiedStateFactory<L,S> mStateFactory;
	private final StratifiedReductionState<L,S> mStartState; 
	private IIndependenceInducedByAbstraction <StratifiedReductionState<L,S>, L> mIndependenceProvider;
	private final ProofManager<L, StratifiedReductionState<L,S>, ? > mProofManager;
	
	private final IDfsOrder<L, S> mOrder;
	private final IDfsVisitor<L, StratifiedReductionState<L,S>> mVisitor;

	private final Deque<Pair<StratifiedReductionState<L,S>, OutgoingInternalTransition<L, StratifiedReductionState<L,S>>>> mWorklist = new ArrayDeque<>();
	private final DfsBookkeeping<StratifiedReductionState<L,S>> mDfs = new DfsBookkeeping<>();
	private HashMap<S,StratifiedReductionState<L,S>> mAlreadyReduced = new HashMap<S, StratifiedReductionState<L,S>>();
	
	private int mIndentLevel = -1;

	/**
	 * Performs a depth-first traversal over the reduction automaton while constructing it. 
	 * This constructor is called purely for its side-effects. (We could also return the finished reduction automaton?)
	 *
	 * @param services
	 *            automata services used for logging and timeout management
	 * @param originalAutomaton
	 *            The automaton to be traversed
	 * @param order
	 *            The order in which transitions for each state should be explored
	 * @param visitor
	 *            A visitor to traverse the automaton
	 * @param startingState
	 *            startingState of the original automaton
	 * @param independence
	 *			provides independence relations for the reduction automaton
	 * @throws AutomataOperationCanceledException
	 *             in case of timeout or cancellation
	 */
	public DynamicStratifiedReduction(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> originalAutomaton, final IDfsOrder<L, S> order,
			final IDfsVisitor<L, StratifiedReductionState<L,S>> visitor, final S startingState, final IIndependenceInducedByAbstraction <StratifiedReductionState<L,S>,L> independence, final ProofManager manager) 
					throws AutomataOperationCanceledException {
		assert NestedWordAutomataUtils.isFiniteAutomaton(originalAutomaton) : "Finite automata only";

		mServices = services;
		mLogger = services.getLoggingService().getLogger(DynamicStratifiedReduction.class);
		mStateFactory = new StratifiedStateFactory<L,S>();
		mOriginalAutomaton = originalAutomaton;
		mReductionAutomaton = new NestedWordAutomaton<L,StratifiedReductionState<L,S>>(services, mOriginalAutomaton.getVpAlphabet(), mStateFactory);
		mStartState = mStateFactory.createStratifiedState(startingState, ImmutableSet.empty(), AbstractionLevel.createEmpty(), 
				AbstractionLevel.createEmpty(), new LinkedList<StratifiedReductionState<L,S>>());
		mOrder = order;
		mIndependenceProvider = independence;
		mVisitor = visitor;
		mProofManager = manager;

		traverse();
	}

	
	/**
	 * builds and traverses the reduction automaton
	 * 
	 * 
	 * 
	 * @throws AutomataOperationCanceledException
	 */

	private void traverse() throws AutomataOperationCanceledException {
		// add initial state to reduction automaton
		mReductionAutomaton.addState(true,mOriginalAutomaton.isFinal(mStateFactory.getOriginalState(mStartState)), mStartState);
		
		createSuccessors(mStartState);
		
		
		
		final boolean abortImmediately = visitState(mStartState);
		if (abortImmediately) {
			mLogger.debug(ABORT_MSG);
			return;
		}

		while (!mWorklist.isEmpty()) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}

			final var current = mWorklist.pop();
			final  StratifiedReductionState<L,S> currentState = current.getFirst();			
			
			//TODO: understand those backtracks
			// Backtrack states still on the stack whose exploration has finished. - what does 'backtrack' mean...
			final boolean abort = backtrackUntil(currentState);
			if (abort) {
				mLogger.debug(ABORT_MSG);
				return;
			}

			final OutgoingInternalTransition<L, StratifiedReductionState<L,S>> currentTransition = current.getSecond();
			final StratifiedReductionState<L,S> nextState = currentTransition.getSucc();
			debugIndent("Now exploring transition %s --> %s (label: %s)", currentState, nextState,
					currentTransition.getLetter());
			final boolean prune = mVisitor.discoverTransition(currentState, currentTransition.getLetter(), nextState);
			if (mVisitor.isFinished()) {
				mLogger.debug(ABORT_MSG);
				return;
			}
			

			final int stackIndex;
			if (prune) {
				debugIndent("-> visitor pruned transition");
			} else if (!mDfs.isVisited(nextState)) {
				createSuccessors(nextState);
				final boolean abortNow = visitState(nextState);
				if (abortNow) {
					mLogger.debug(ABORT_MSG);
					return;
				}
			} else if ((stackIndex = mDfs.stackIndexOf(nextState)) != -1) {
				// TODO: check if this loop is allowed, otherwise to a loop exploration
				debugIndent("-> state is on stack -- do not unroll loop");
				mDfs.updateLoopHead(currentState, new Pair<>(stackIndex, nextState));
			} else {
				// TODO: it's not that easy anymore, we need to check if a copy exploration is necessary
				ImmutableSet<L> newSleepSet = createSleepSet(currentState, currentTransition.getLetter());
				
				// If the sleepsets are inequal or the abstraction level of the next state is higher than our current abstraction level we need to copy the state
				boolean copyState = ((newSleepSet != mStateFactory.getSleepSet(nextState)) || 
						!(mStateFactory.getAbstractionLevel(currentState).isLEQ(mStateFactory.getAbstractionLevel(nextState))));
				if(copyState) {
					debugIndent("-> state's abstraction level or sleepset are unfitting -- copying state");

					
					
				} else {
					debugIndent("-> state was visited before -- no re-exploration");
					mDfs.backPropagateLoopHead(currentState, nextState);
				}
			}
		}// end while

		final boolean abort = backtrackUntil(mStartState);
		if (abort) {
			mLogger.debug(ABORT_MSG);
			return;
		}

		backtrack();
		mLogger.debug("traversal completed");
	}

	private boolean backtrackUntil(final StratifiedReductionState<L,S> state) {
		while (!mDfs.peek().equals(state)) {
			final boolean abort = backtrack();
			if (abort) {
				return true;
			}
		}
		return false;
	}
	
	//TODO: Update Abstraction Levels here?

	private boolean backtrack() {
		final StratifiedReductionState<L,S> oldState = mDfs.peek();
		final boolean isComplete = mDfs.backtrack();

		debugIndent("backtracking state %s (complete: %s)", oldState, isComplete);
		mIndentLevel--;
		// give its Abstractionlevel to its parents?
		mVisitor.backtrackState(oldState, isComplete);
		return mVisitor.isFinished();
	}

	
	// need to create state's outgoing transitions and successors before this
	// check if its a proven state, if so update abstraction level
	private boolean visitState(final StratifiedReductionState<L,S> state) {
		assert !mDfs.isVisited(state) : "must never re-visit state";
		mIndentLevel++;
		debugIndent("visiting state %s", state);
		
		boolean isProvenState = mProofManager.isProvenState(state);
		if (isProvenState) {
			HashSet<L> freeVars = mProofManager.getVariables(mProofManager.choseRespProof(state));
			mStateFactory.addToAbstractionLevel(state, freeVars);
			// how can i modify states of the nested word automaton???
		}
		
		
		final boolean pruneSuccessors;
		if (mStartState.equals(state)) {
			debugIndent("-> state is start state");
			assert !mDfs.hasStarted() : "start state should be first visited state";
			pruneSuccessors = mVisitor.addStartState(state);
		} else {
			assert mDfs.hasStarted() : "first visited state should be start state";
			pruneSuccessors = mVisitor.discoverState(state);
		}
		if (mVisitor.isFinished()) {
			return true;
		}
		mDfs.push(state);

		if (pruneSuccessors) {
			debugIndent("-> visitor pruned all outgoing edges");
		} else {
			final Comparator<OutgoingInternalTransition<L, StratifiedReductionState<L,S>>> comp =
					Comparator.<OutgoingInternalTransition<L, StratifiedReductionState<L,S>>, L> comparing(OutgoingInternalTransition::getLetter,
							mOrder.getOrder(mStateFactory.getOriginalState(state))).reversed();
			StreamSupport.stream(mReductionAutomaton.internalSuccessors(state).spliterator(), false).sorted(comp)
					.forEachOrdered(out -> mWorklist.push(new Pair<>(state, out)));
		}
		return false;
	}

	private void debugIndent(final String msg, final Object... params) {
		mLogger.debug("  ".repeat(mIndentLevel) + msg, params);
	}
	
	
	
	
// Stuff for reductionbuilding	
	/**
	 *  get original successor states & transitions and add their reduction states/transitions to the reduction automaton
	 * @param state		state whose successors are created
	 */
	
	private void createSuccessors(StratifiedReductionState<L,S> state) {
		S originalState = mStateFactory.getOriginalState(state);
		
		ImmutableSet<L> toPrune = mStateFactory.getSleepSet(state);
		Iterator<L> outgoingLetters = mOriginalAutomaton.lettersInternal(originalState).iterator();
		while (outgoingLetters.hasNext()) {
			L letter = outgoingLetters.next();
			S originalSucc = mOriginalAutomaton.internalSuccessors(originalState, letter).iterator().next().getSucc();
			if(!toPrune.contains(letter)){
				StratifiedReductionState<L,S > correspRstate = mAlreadyReduced.get(originalState); 
				/* If there is no reduction state corresponding to this state of the original automaton or its corresponding reduction state is in the already completed part of the 
				 * reduction automaton and therefore has a higher abstraction level than our current state we create a new reduction state.*/
				
				if (correspRstate != null | mStateFactory.getAbstractionLevel(correspRstate).isLocked()) {
					ImmutableSet<L> nextSleepSet = createSleepSet(state, letter);
					StratifiedReductionState<L,S> reductionSucc = createNextState(state, nextSleepSet, originalSucc, letter);
					mReductionAutomaton.addState(mOriginalAutomaton.isInitial(originalSucc), mOriginalAutomaton.isFinal(originalSucc), reductionSucc);
					mReductionAutomaton.addInternalTransition(state, letter, reductionSucc);
					mAlreadyReduced.remove(originalSucc);    // old reduction state will be replaced by its copy
					mAlreadyReduced.put(originalSucc, reductionSucc);
				} 
				/* If we are inside a loop we first check if the loop edge from our current state to the existing reduction state is legal. If so we simply add it to the 
				 * reduction automaton, if not we start building a loop copy.*/
				
				else if(((!mStateFactory.isLoopCopy(state)) & mStateFactory.getLoopablePredecs(state).contains(correspRstate))
					| (mStateFactory.isLoopCopy(state) & (mStateFactory.getAbstractionLevel(state).getValue() == mStateFactory.getAbstractionLimit(correspRstate).getValue()))){
					// if the abstraction level of the corresp. red. state is not yet defined it is still on the stack -> we're in a loop
					mReductionAutomaton.addInternalTransition(state, letter, correspRstate);	
				} else {
					// create a copystate with fixed abstractionlimit for its subgraph
					ImmutableSet<L> nextSleepSet = createSleepSet(state, letter);
					AbstractionLevel<L> nextAbstractionLimit = new AbstractionLevel(mStateFactory.getAbstractionLevel(state).getValue(), true);
					AbstractionLevel<L> nextAbstractionLevel = new AbstractionLevel(nextAbstractionLimit.getValue(), true);
					StratifiedReductionState<L,S> reductionSucc = mStateFactory.createStratifiedState(originalState, nextSleepSet, 
							nextAbstractionLevel, nextAbstractionLimit, new LinkedList());
					mReductionAutomaton.addState(mOriginalAutomaton.isInitial(originalSucc), mOriginalAutomaton.isFinal(originalSucc), reductionSucc);
					mReductionAutomaton.addInternalTransition(state, letter, reductionSucc);
					mAlreadyReduced.remove(originalSucc);    		// old reduction state will be replaced by its copy
					mAlreadyReduced.put(originalSucc, reductionSucc);
				}
			}
		}
	}
	
	
	
	/* *
	 * create the sleep set for a state of the reduction automaton
	 * 
	 * @param current
	 * 			The current state of the reduction automaton
	 * @param letter
	 * 			The letter on the transition from the current state to the state whose sleepset is being created
	 */
	private ImmutableSet<L> createSleepSet( StratifiedReductionState<L,S> current, L letter) {
		
		final S currentS = mStateFactory.getOriginalState(current);
		final ImmutableSet<L> currSleepSet = mStateFactory.getSleepSet(current);
		IIndependenceRelation<StratifiedReductionState<L,S>,L> Independence = mIndependenceProvider.getInducedIndependence(mStateFactory.getAbstractionLevel(current).getValue());
		
		// stolen from minimal sleep set reduction
		
		final Comparator<L> comp = mOrder.getOrder(currentS);
		final Stream<L> explored = mOriginalAutomaton.lettersInternal(currentS).stream()
				.filter(x -> comp.compare(x, letter) < 0 && !currSleepSet.contains(x));
		
		//TODO: check if this is ok
		
		final HashSet<L> protVar = (HashSet<L>) Set.of(Stream.concat(currSleepSet.stream(), explored)
				.filter(l -> Independence.isIndependent(current, letter, l) == Dependence.INDEPENDENT)
				.toArray());
		final ImmutableSet<L> sleepSet =
				ImmutableSet.of((Set<L>) Set.of(Stream.concat(currSleepSet.stream(), explored)
						.filter(l -> Independence.isIndependent(current, letter, l) == Dependence.INDEPENDENT)
						.toArray()));
		
		return sleepSet;
		}
	
	/**
	 * Create a newly discovered state of the reduction automaton
	 * 
	 * 
	 * @param predecState
	 * 			State of the reduction automaton from which the new state was discovered
	 * @param sleepSet
	 * 			Sleep set of the new state
	 * @param originState
	 * 			State of the original automaton that corresponds to the new state
	 * @param letter
	 * 			Letter of the transition leading to the new state
	 * 
	 * @return
	 * 		The reduction state
	 */	
	
		private StratifiedReductionState<L,S> createNextState(StratifiedReductionState<L,S> predecState, ImmutableSet<L> sleepSet, S originState, L letter) { 

			LinkedList<StratifiedReductionState<L,S>> loopablepredecs = new LinkedList<StratifiedReductionState<L,S>>();
			
			// If the current transition is the smallest (unpruned) outgoing transition of the state let it 'inherit' the list of loopable predecessors 

			final Stream<L> smallerEdges = mOriginalAutomaton.lettersInternal(originState).stream()
					.filter(x -> mOrder.getOrder(originState).compare(x, letter) < 0 && !mStateFactory.getSleepSet(predecState).contains(x));
			if(smallerEdges.findAny().isEmpty()) {
				loopablepredecs.addAll(mStateFactory.getLoopablePredecs(predecState));
				loopablepredecs.add(predecState);
			}
				
			
			// Abstraction limit of the new state is the abstraction limit of its parent + the abstraction levels of the edges in its sleepset
			HashSet<L> protectedVars = mStateFactory.getAbstractionLimit(predecState).getValue();
			
			Iterator<L> comEdges = sleepSet.iterator();
			
			while(comEdges.hasNext()) {
				StratifiedReductionState<L,S> succState = mReductionAutomaton.internalSuccessors(predecState, comEdges.next()).iterator().next().getSucc();
				protectedVars.addAll(mStateFactory.getAbstractionLevel(succState).getValue());		
			}
			
			return new StratifiedReductionState<L,S>(originState, sleepSet, new AbstractionLevel<L>(protectedVars, mStateFactory.getAbstractionLimit(predecState).isLocked()), 
					new AbstractionLevel<L>(protectedVars, false), loopablepredecs);
		}
}
	
	