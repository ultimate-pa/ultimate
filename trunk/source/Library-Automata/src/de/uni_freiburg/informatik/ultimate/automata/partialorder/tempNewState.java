package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class tempNewState<L, S, S2> {
	
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final Set<S> mStartStateSet;
	private final Set<S2> mVisitedSet;
	private final ArrayDeque<S2> mStateStack;
	private final HashMap<S2, Pair<S, Set<L>>> mStateMap;
	private final ISleepSetOrder<S, L> mOrder;
	private final IIndependenceRelation<S, L> mIndependenceRelation;
	private final ISleepSetStateFactory<L, S, S2> mStateFactory;
	private final IPartialOrderVisitor<L, S> mVisitor;
	private boolean mExit;
	private final Set<S2> mCompletedSet;
	private final HashMap<S2, Set<L>> mExploredMap;

	public tempNewState(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IIndependenceRelation<S, L> independenceRelation, final ISleepSetOrder<S, L> sleepSetOrder,
			final ISleepSetStateFactory<L, S, S2> stateFactory, final IPartialOrderVisitor<L, S> visitor) {
		mStateFactory = stateFactory;
		mOperand = operand;
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "Sleep sets support only finite automata";

		mStartStateSet = CoreUtil.constructHashSet(operand.getInitialStates());
		assert (mStartStateSet.size() == 1) : "Only one initial state allowed";

		mVisitedSet = new HashSet<>();
		mStateStack = new ArrayDeque<>();
		mStateMap = new HashMap<>();
		mVisitor = visitor;
		mExit = false;
		mCompletedSet = new HashSet<>();
		mExploredMap = new HashMap<>();
		for (final S startState : mStartStateSet) {
			final Set<L> emptySet = new HashSet<>();
			final Pair<S, Set<L>> startStatePair = new Pair<>(startState, emptySet);
			final S2 newStartState = stateFactory.createSleepSetState(startState, emptySet);
			mExit = mVisitor.addStartState(startState);
			mStateStack.push(newStartState);
			mStateMap.put(newStartState, startStatePair);

		}
		mOrder = sleepSetOrder;
		mIndependenceRelation = independenceRelation;
		search();
	}

	private void search() {

		while (!mExit && !mStateStack.isEmpty()) {

			final S2 currentSleepSetState = mStateStack.pop();
			final ArrayList<L> successorTransitionList = new ArrayList<>();
			final S currentState = mStateMap.get(currentSleepSetState).getFirst();
			final Set<L> currentSleepSet = mStateMap.get(currentSleepSetState).getSecond();
			
			if (!mVisitedSet.contains(currentSleepSetState)) {
				mVisitedSet.add(currentSleepSetState);
				mExploredMap.put(currentSleepSetState, new HashSet<L>());
			}

			if (!mCompletedSet.contains(currentSleepSetState) && !mStateStack.contains(currentSleepSetState)) {
				// state not visited with this sleep set
				//mVisitor.discoverState(currentState);
				
				for (final OutgoingInternalTransition<L, S> transition : mOperand.internalSuccessors(currentState)) {
					if (!currentSleepSet.contains(transition.getLetter())
							&& !mExploredMap.get(currentSleepSetState).contains(transition.getLetter())) {
						successorTransitionList.add(transition.getLetter());
					}
				}
				if (!successorTransitionList.isEmpty()) {
					final Comparator<L> order = mOrder.getOrder(currentState);
					successorTransitionList.sort(order);
					L transition = successorTransitionList.get(0);
					
					final var successors = mOperand.internalSuccessors(currentState, transition).iterator();
					if (!successors.hasNext()) {
						continue;
					}
					final var currentTransition = successors.next();
					assert !successors.hasNext() : "Automaton must be deterministic";

					final S succState = currentTransition.getSucc();
					Set<L> explored = mExploredMap.get(currentSleepSetState);
					final Set<L> succSleepSet = DataStructureUtils.union(currentSleepSet, explored).stream()
							.filter(l -> mIndependenceRelation.contains(currentState, transition, l))
							.collect(Collectors.toCollection(HashSet::new));
					final S2 succSleepSetState = mStateFactory.createSleepSetState(succState, succSleepSet);
					mStateMap.put(succSleepSetState, new Pair<>(succState, succSleepSet));
					mExit = mVisitor.discoverTransition(currentState, transition, succState);
					mStateStack.push(currentSleepSetState);
					mStateStack.push(succSleepSetState);
					explored.add(transition);
					mExploredMap.put(currentSleepSetState, explored);			
				} else {
					mVisitor.backtrackState(currentState);
					mCompletedSet.add(currentSleepSetState);
				}
			} else {
				mVisitor.backtrackState(currentState);
			}

		}
	}

}
