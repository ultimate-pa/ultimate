/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.AbstractList;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeatureExtractionTermClassifier.ScoringMethod;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashedPriorityQueue;

/**
 * Check emptiness and obtain an accepting run of a nested word automaton using a modified version of A*.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class IsEmptyHeuristic<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {

	private static final boolean DEBUG_MESSAGES_USE_HASHCODE = false;

	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private final Predicate<STATE> mIsGoalState;
	private final Predicate<STATE> mIsForbiddenState;
	private final NestedRun<LETTER, STATE> mAcceptingRun;
	private final STATE mDummyEmptyStackState;

	private final IHeuristic<STATE, LETTER> mHeuristic;

	/**
	 * Default constructor. Here we search a run from the initial states of the automaton to the final states of the
	 * automaton and use the zero heuristic.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            input NWA
	 * @see #IsEmpty(AutomataLibraryServices, INwaOutgoingLetterAndTransitionProvider)
	 */
	public IsEmptyHeuristic(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		this(services, operand, IHeuristic.getZeroHeuristic());
	}

	/**
	 * Default constructor. Here we search a run from the initial states of the automaton to the final states of the
	 * automaton and use the zero heuristic.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            input NWA
	 * @see #IsEmpty(AutomataLibraryServices, INwaOutgoingLetterAndTransitionProvider)
	 */
	public IsEmptyHeuristic(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final IHeuristic<STATE, LETTER> heuristic) throws AutomataOperationCanceledException {
		this(services, operand, CoreUtil.constructHashSet(operand.getInitialStates()), a -> false, operand::isFinal,
				heuristic);
	}

	/**
	 * Constructor that is not restricted to emptiness checks. The set of startStates defines where the run that we
	 * search has to start. The set of forbiddenStates defines states that the run must not visit. The set of goalStates
	 * defines where the run that we search has to end.
	 */
	public IsEmptyHeuristic(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> operand,
			final Set<STATE> startStates, final Predicate<STATE> funIsForbiddenState,
			final Predicate<STATE> funIsGoalState, final IHeuristic<STATE, LETTER> heuristic)
			throws AutomataOperationCanceledException {
		this(services, (INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>) operand, startStates,
				funIsForbiddenState, funIsGoalState, heuristic);
		assert operand.getStates().containsAll(startStates) : "unknown states";
	}

	private IsEmptyHeuristic(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand, final Set<STATE> startStates,
			final Predicate<STATE> funIsForbiddenState, final Predicate<STATE> funIsGoalState,
			final IHeuristic<STATE, LETTER> heuristic) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mIsGoalState = funIsGoalState;
		mIsForbiddenState = funIsForbiddenState;
		mHeuristic = heuristic;

		assert startStates != null;
		assert mIsGoalState != null;
		assert mIsForbiddenState != null;
		assert mOperand != null;

		mDummyEmptyStackState = mOperand.getEmptyStackState();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mAcceptingRun = getAcceptingRun(startStates, heuristic);

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	/**
	 * Get an accepting run of the automaton passed to the constructor. Return null if the automaton does not accept any
	 * nested word.
	 *
	 * @param heuristic
	 */
	private NestedRun<LETTER, STATE> getAcceptingRun(final Collection<STATE> startStates,
			final IHeuristic<STATE, LETTER> heuristic) throws AutomataOperationCanceledException {

		final HashedPriorityQueue<Item> worklist =
				new HashedPriorityQueue<>((a, b) -> Double.compare(a.mEstimatedCostToTarget, b.mEstimatedCostToTarget));

		for (final STATE state : startStates) {
			final Item initialItem = new Item(state);
			initialItem.setCostSoFar(0.0);
			worklist.add(initialItem);
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(String.format("Initial queue: %s", worklist));
		}

		// TODO: Two separate maps, one for call, one for internal/return
		final Map<Item, Double> lowestOther = new HashMap<>();
		final Map<Item, Double> lowestCall = new HashMap<>();
		final Map<STATE, Set<STATE>> discoveredUniqueReturnStates = new HashMap<>();
		final Map<STATE, Set<Item>> delayedCalls = new HashMap<>();
		final Map<CallTransition, Map<ReturnTransition, SummaryItem>> summaries = new HashMap<>();
		final Map<CallTransition, Map<ReturnTransition, Set<Item>>> usedSummaries = new HashMap<>();

		while (!worklist.isEmpty()) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				final String taskDescription = "searching accepting run (input had " + mOperand.size() + " states)";
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(), taskDescription);
				throw new AutomataOperationCanceledException(rti);
			}

			final Item current = worklist.poll();

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(String.format("Current: %s", current));
			}
			final List<Item> stragglingSummaries;
			if (current.mItemType == ItemType.RETURN) {
				stragglingSummaries = updateSummaries(summaries, usedSummaries, current);
			} else {
				stragglingSummaries = Collections.emptyList();
			}

			final List<Item> unvaluatedSuccessors =
					getUnvaluatedSuccessors(current, discoveredUniqueReturnStates, delayedCalls);
			if (mLogger.isDebugEnabled() && unvaluatedSuccessors.isEmpty()) {
				mLogger.debug("  No successors");
				continue;
			}

			final List<Item> successors =
					addCostAndSummaries(unvaluatedSuccessors, summaries, usedSummaries, heuristic, current.mCostSoFar);
			successors.addAll(stragglingSummaries);

			if (heuristic instanceof SmtFeatureHeuristic && ((SmtFeatureHeuristic<STATE, LETTER>) heuristic)
					.getScoringMethod() == ScoringMethod.COMPARE_FEATURES) {
				((SmtFeatureHeuristic<STATE, LETTER>) heuristic).compareSuccessors(successors);
			}

			for (final Item succ : successors) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(String.format("  Succ: %s", succ));
				}

				final double costSoFar = succ.mCostSoFar;

				final Double lowestCostSoFar;
				if (succ.mItemType == ItemType.CALL) {
					lowestCostSoFar = lowestCall.get(succ);
				} else {
					lowestCostSoFar = lowestOther.get(succ);
				}

				if (lowestCostSoFar != null && costSoFar >= lowestCostSoFar) {
					// we have already seen this successor but with a lower
					// cost, so we should not explore with a
					// higher cost
					if (mLogger.isDebugEnabled()) {
						mLogger.debug(String.format("    Skip (cost %s, but have seen with cost %s)", costSoFar,
								lowestCostSoFar));
					}
					continue;
				}
				if (succ.mItemType == ItemType.CALL
						&& !isCheapestAncestor(lowestCall, discoveredUniqueReturnStates, succ, costSoFar)) {
					// if the succ is not yet in lowest, there can still be an
					// item with a call stack that has the
					// same ancestor as the current succ -- if this item is
					// cheaper, we do not insert.
					// TODO: isCheapestAncestor is rather expensive, but with a
					// dedicated data structure it could be
					// much cheaper, e.g., something similar to a suffix tree
					delayedCalls.computeIfAbsent(current.getHierPreState(), a -> new LinkedHashSet<>()).add(succ);
					continue;
				}

				final double expectedCostToTarget =
						heuristic.getHeuristicValue(succ.mTargetState, succ.getHierPreState(), succ.mLetter);
				succ.setEstimatedCostToTarget(expectedCostToTarget);

				// we changed the cost of this item, so we have to remove it if
				// it is already in the queue, because
				// its queue position will not be updated otherwise
				if (worklist.remove(succ)) {
					if (mLogger.isDebugEnabled()) {
						mLogger.debug(String.format("    Updated: %s", succ));
					}
				} else if (mLogger.isDebugEnabled()) {
					mLogger.debug(String.format("    Insert: %s", succ));
				}
				worklist.add(succ);
				if (succ.mItemType == ItemType.CALL) {
					lowestCall.put(succ, costSoFar);
				} else {
					lowestOther.put(succ, costSoFar);
				}
			}
		}
		if (mLogger.isDebugEnabled())

		{
			printDebugStats(lowestCall, lowestOther, summaries);
		}
		return null;
	}

	private void printDebugStats(final Map<Item, Double> lowestCall, final Map<Item, Double> lowestOther,
			final Map<CallTransition, Map<ReturnTransition, SummaryItem>> summaries) {
		mLogger.debug(String.format("Found %d lowest call configurations", lowestCall.size()));
		mLogger.debug(String.format("Found %d lowest configurations", lowestOther.size()));
		mLogger.debug(String.format("Found summaries for %d calls", summaries.size()));
		mLogger.debug(String.format("Summary size histogram: [%s]",
				summaries.entrySet().stream().map(a -> a.getValue().size()).sorted((a, b) -> -Integer.compare(a, b))
						.map(String::valueOf).collect(Collectors.joining(","))));
	}

	private List<Item> addCostAndSummaries(final List<Item> succs,
			final Map<CallTransition, Map<ReturnTransition, SummaryItem>> summaries,
			final Map<CallTransition, Map<ReturnTransition, Set<Item>>> usedSummaries,
			final IHeuristic<STATE, LETTER> heuristic, final double currentCostSoFar) {

		final List<Item> newSuccs = new ArrayList<>(2 * succs.size());
		for (final Item succ : succs) {
			if (succ.mCostSoFar >= 0.0) {
				// these are delayed calls
				newSuccs.add(succ);
				continue;
			}

			final double concreteCost = heuristic.getConcreteCost(succ.mLetter);

			if (succ.mItemType == ItemType.CALL) {
				final CallTransition callTrans = new CallTransition(succ);
				final Map<ReturnTransition, SummaryItem> summary = summaries.get(callTrans);
				if (summary != null) {
					assert !summary.isEmpty();
					// there is a summary for this call and we are going to use
					// it.
					// we need to record that we used a summary in case we find
					// more summaries later (straggling
					// summaries)
					// we save the cost of the current location in the successor
					// item, so we may use it for straggling
					// summaries
					succ.setCostSoFar(currentCostSoFar + concreteCost);
					final Map<ReturnTransition, Set<Item>> usedSummariesForCall =
							usedSummaries.computeIfAbsent(callTrans, a -> new HashMap<>());
					for (final Entry<ReturnTransition, SummaryItem> entry : summary.entrySet()) {
						final SummaryItem sumItem = entry.getValue();
						final Item newSucc = new Item(succ, sumItem);
						newSucc.setCostSoFar(succ.mCostSoFar + sumItem.mSummaryCost);
						newSuccs.add(newSucc);

						usedSummariesForCall.computeIfAbsent(entry.getKey(), a -> new LinkedHashSet<>()).add(succ);
						if (mLogger.isDebugEnabled()) {
							mLogger.debug(String.format("  Using summary %s instead of %s", sumItem, succ));
							mLogger.debug(String.format("    Subrun: %s ", sumItem.mSubrun));
						}
					}
					continue;
				}
			}

			succ.setCostSoFar(currentCostSoFar + concreteCost);
			newSuccs.add(succ);
		}

		return newSuccs;
	}

	private List<Item> updateSummaries(final Map<CallTransition, Map<ReturnTransition, SummaryItem>> summaries,
			final Map<CallTransition, Map<ReturnTransition, Set<Item>>> usedSummaries, final Item returnItem) {

		// the current item is a return (returnItem), so we can compute a new
		// summary

		final Item callItem = returnItem.findCorrespondingCallItem();
		final CallTransition callTrans = new CallTransition(callItem);
		final ReturnTransition returnTrans = new ReturnTransition(returnItem);
		final Map<ReturnTransition, SummaryItem> oldSummaries =
				summaries.computeIfAbsent(callTrans, k -> new HashMap<>());

		final SummaryItem oldSummary = oldSummaries.get(returnTrans);
		if (oldSummary == null) {
			final SummaryItem sItem = new SummaryItem(returnItem, callItem);
			oldSummaries.put(returnTrans, sItem);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(String.format("  Is fresh summary: %s", sItem));
			}

			// if we add a fresh summary, we also have to add additional items
			// to the worklist for all the items that
			// already used summaries of this call
			final Map<ReturnTransition, Set<Item>> usedSummariesForCall = usedSummaries.get(callTrans);
			if (usedSummariesForCall != null) {
				final List<Item> rtr = new ArrayList<>();
				for (final Entry<ReturnTransition, Set<Item>> entry : usedSummariesForCall.entrySet()) {
					for (final Item oldItem : entry.getValue()) {
						final Item i = new Item(oldItem, sItem);
						i.setCostSoFar(oldItem.mCostSoFar + sItem.mSummaryCost);
						rtr.add(i);
					}
				}
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(String.format("  Re-added %d items for the fresh summary", rtr.size()));
				}
				return rtr;

			}
			return Collections.emptyList();
		}
		final double summaryCost = returnItem.mCostSoFar - callItem.mCostSoFar;
		if (summaryCost < oldSummary.mSummaryCost) {
			final SummaryItem sItem = new SummaryItem(returnItem, callItem);
			oldSummaries.put(returnTrans, sItem);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(String.format("  Found cheaper summary (old cost was %s, new is %s): %s",
						oldSummary.mSummaryCost, summaryCost, sItem));
			}
		} else if (mLogger.isDebugEnabled()) {
			mLogger.debug(String.format("  Will not replace old summary (cost %s) with this one (cost %s)",
					oldSummary.mSummaryCost, summaryCost));
		}
		return Collections.emptyList();
	}

	private boolean isCheapestAncestor(final Map<Item, Double> lowest,
			final Map<STATE, Set<STATE>> discoveredUniqueReturnStates, final Item succ, final double costSoFar) {
		assert succ.mItemType == ItemType.CALL : "It only makes sense to check Calls for cheapest ancestor";
		for (final Entry<Item, Double> entry : lowest.entrySet()) {
			final Item item = entry.getKey();

			if (!item.mLetter.equals(succ.mLetter)) {
				// we only need to check against the same transition
				continue;
			}

			if (!Objects.equals(item.getBackpointer().getTargetState(), succ.getBackpointer().getTargetState())) {
				continue;
			}

			final double lowestCostSoFar = entry.getValue();
			if (item.mHierPreStates.size() >= succ.mHierPreStates.size()) {
				// item cannot be prefix, is either longer, or, if it is the
				// same length, has a different
				// hashcode (checked before)
				continue;
			}
			final int extension =
					discoveredUniqueReturnStates.getOrDefault(succ.getHierPreState(), Collections.emptySet()).size();
			if (item.isHierStatesPrefixOf(succ, extension) && costSoFar >= lowestCostSoFar) {
				// we have already seen this successor but with a lower cost, so
				// we should not explore
				// with a higher cost
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(String.format(
							"    Skip for now (cost %s, but have seen %d-extended prefix with cost %s: %s)", costSoFar,
							extension, lowestCostSoFar, item));
				}
				return false;
			}
		}
		return true;
	}

	private List<Item> getUnvaluatedSuccessors(final Item current,
			final Map<STATE, Set<STATE>> discoveredUniqueReturnStates, final Map<STATE, Set<Item>> delayedCalls) {
		final List<Item> rtr = new ArrayList<>();

		// process internal transitions
		for (final OutgoingInternalTransition<LETTER, STATE> transition : mOperand
				.internalSuccessors(current.mTargetState)) {
			final LETTER symbol = transition.getLetter();
			final STATE succ = transition.getSucc();
			if (mIsForbiddenState.test(succ)) {
				continue;
			}
			rtr.add(new Item(succ, current.getHierPreState(), symbol, current, ItemType.INTERNAL));
		}

		// process call transitions
		for (final OutgoingCallTransition<LETTER, STATE> transition : mOperand.callSuccessors(current.mTargetState)) {
			final LETTER symbol = transition.getLetter();
			final STATE succ = transition.getSucc();
			if (mIsForbiddenState.test(succ)) {
				continue;
			}
			rtr.add(new Item(succ, current.mTargetState, symbol, current, ItemType.CALL));
		}

		final STATE hierPre = current.getHierPreState();
		if (hierPre == null || hierPre == mDummyEmptyStackState) {
			// there is no (valid) return transition
			return rtr;
		}

		final int old = rtr.size();
		// process return transitions
		for (final OutgoingReturnTransition<LETTER, STATE> transition : mOperand
				.returnSuccessorsGivenHier(current.mTargetState, hierPre)) {
			final LETTER symbol = transition.getLetter();
			final STATE succ = transition.getSucc();
			if (mIsForbiddenState.test(succ)) {
				continue;
			}
			// hierarchical predecessor will be taken from current
			rtr.add(new Item(succ, null, symbol, current, ItemType.RETURN));
		}
		if (old != rtr.size()) {
			// we found a new state from which a hierPre call can take at least
			// one return
			discoveredUniqueReturnStates.computeIfAbsent(hierPre, a -> new HashSet<>()).add(current.mTargetState);

			final Set<Item> hierDelayedCalls = delayedCalls.remove(hierPre);
			if (hierDelayedCalls != null) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(String.format("  Re-adding %d delayed calls", hierDelayedCalls.size()));
				}
				rtr.addAll(hierDelayedCalls);
			}
		}
		return rtr;
	}

	private double recomputeCost(final NestedRun<LETTER, STATE> run) {
		return run.getWord().asList().stream().collect(Collectors.summingDouble(mHeuristic::getConcreteCost));
	}

	private boolean checkCost(final double expectedCost, final NestedRun<LETTER, STATE> run) {
		if (expectedCost < 0.0) {
			mLogger.fatal("Cost must be positive or zero");
			return false;
		}
		final double recomputedCost = recomputeCost(run);
		if (expectedCost != recomputedCost) {
			mLogger.fatal("Cost is not sum of concrete cost");
			return false;
		}
		return true;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mAcceptingRun == null;
	}

	public NestedRun<LETTER, STATE> getNestedRun() {
		return mAcceptingRun;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (mAcceptingRun == null) {
			final boolean isEmpty = new IsEmpty<>(mServices, mOperand).getResult();
			if (!isEmpty) {
				mLogger.fatal("IsEmpty found an accepting run and " + getClass().getSimpleName() + " did not");
			}
			return isEmpty;
		}
		final boolean accepts = new Accepts<>(mServices, mOperand, mAcceptingRun.getWord()).getResult();
		if (!accepts) {
			mLogger.fatal(getClass().getSimpleName() + " found a run, but it is not accepted");
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Run is " + mAcceptingRun);
		}
		return accepts;
	}

	@Override
	public String exitMessage() {
		if (mAcceptingRun == null) {
			return "Finished " + getOperationName() + ". No accepting run.";
		}
		return "Finished " + getOperationName() + ". Found accepting run of length " + mAcceptingRun.getLength();
	}

	private enum ItemType {
		CALL, RETURN, INTERNAL, INITIAL
	}

	private class ReturnTransition {
		private final STATE mTargetState;
		private final LETTER mTransition;
		private final int mHash;

		private ReturnTransition(final Item item) {
			mTransition = item.mLetter;
			mTargetState = item.mTargetState;
			mHash = HashUtils.hashHsieh(31, mTargetState, mTransition);
		}

		@Override
		public int hashCode() {
			return mHash;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			@SuppressWarnings("unchecked")
			final ReturnTransition other = (ReturnTransition) obj;
			if (!mTargetState.equals(other.mTargetState)) {
				return false;
			}
			return mTransition.equals(other.mTransition);
		}
	}

	private class CallTransition {
		private final STATE mTargetState;
		private final STATE mHierPreState;
		private final LETTER mTransition;
		private final int mHash;

		private CallTransition(final Item item) {
			mTransition = item.mLetter;
			mTargetState = item.mTargetState;
			mHierPreState = item.getHierPreState();
			mHash = HashUtils.hashHsieh(31, mHierPreState, mTargetState, mTransition);
		}

		@Override
		public int hashCode() {
			return mHash;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			@SuppressWarnings("unchecked")
			final CallTransition other = (CallTransition) obj;
			if (!mHierPreState.equals(other.mHierPreState)) {
				return false;
			}
			if (!mTargetState.equals(other.mTargetState)) {
				return false;
			}
			return mTransition.equals(other.mTransition);
		}
	}

	private interface IWithBackPointer<STATE> {
		IWithBackPointer<STATE> getBackpointer();

		STATE getTargetState();
	}

	private class SummaryItem implements IWithBackPointer<STATE> {

		// the actual cost of this summary, i.e., the cost of the subpath in
		// this summary
		private final double mSummaryCost;
		private final NestedRun<LETTER, STATE> mSubrun;
		private final IWithBackPointer<STATE> mBackPointer;
		private final Item mReturnItem;

		public SummaryItem(final Item returnItem, final Item callItem) {
			this(returnItem.mCostSoFar - callItem.mCostSoFar, returnItem.constructRun(a -> a == callItem, true),
					returnItem, callItem);
		}

		public SummaryItem(final Item callItem, final SummaryItem summary) {
			this(summary.mSummaryCost, summary.mSubrun, summary.mReturnItem, callItem);
		}

		private SummaryItem(final double summaryCost, final NestedRun<LETTER, STATE> subrun, final Item returnItem,
				final IWithBackPointer<STATE> backPointer) {
			mSummaryCost = summaryCost;
			mSubrun = subrun;
			mReturnItem = returnItem;
			mBackPointer = backPointer;
			assert mSubrun != null : "Summary must have subrun";
			assert checkCost(mSummaryCost, mSubrun) : "Summary cost is wrong";
		}

		@Override
		public IWithBackPointer<STATE> getBackpointer() {
			return mBackPointer;
		}

		@Override
		public STATE getTargetState() {
			return mSubrun.getStateAtPosition(mSubrun.getLength());
		}

		@Override
		public String toString() {
			return String.format(" Summary for {%s} to {%s} (cost=%s)", mBackPointer, mReturnItem, mSummaryCost);
		}

		@Override
		public int hashCode() {
			return 31 + mReturnItem.hashCode();
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			@SuppressWarnings("unchecked")
			final SummaryItem other = (SummaryItem) obj;
			return mReturnItem.equals(other.mReturnItem);
		}
	}

	/**
	 * Internal datastructure that represents worklist item.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public class Item implements Comparable<Item>, IWithBackPointer<STATE> {

		private final STATE mTargetState;
		private final Deque<STATE> mHierPreStates;
		private final LETTER mLetter;
		private final IWithBackPointer<STATE> mBackPointer;
		private final ItemType mItemType;
		private final int mHashCode;

		// g-value, how much have we already payed?
		private double mCostSoFar;
		// h-value, i.e., how expensive from here to target using this node
		private double mEstimatedCostToTargetFromHere;
		// f-value, i.e. how expensive from start to target if we use this node,
		// i.e. g+h
		private double mEstimatedCostToTarget;

		/**
		 * Create initial worklist item.
		 */
		private Item(final STATE initialState) {
			this(initialState, mDummyEmptyStackState, null, null, ItemType.INITIAL);
		}

		/**
		 * Create new worklist item.
		 */
		private Item(final STATE targetState, final STATE hierPreState, final LETTER letter, final Item predecessor,
				final ItemType symbolType) {
			mTargetState = targetState;
			if (symbolType == ItemType.INTERNAL) {
				mHierPreStates = predecessor.mHierPreStates;
			} else if (symbolType == ItemType.RETURN) {
				mHierPreStates = new ElementHashedArrayDeque<>(predecessor.mHierPreStates);
				mHierPreStates.pop();
			} else if (symbolType == ItemType.CALL) {
				mHierPreStates = new ElementHashedArrayDeque<>(predecessor.mHierPreStates);
				mHierPreStates.push(hierPreState);
			} else {
				mHierPreStates = new ElementHashedArrayDeque<>();
				mHierPreStates.push(hierPreState);
			}

			mLetter = letter;
			mBackPointer = predecessor;
			mItemType = symbolType;

			mCostSoFar = -1.0;
			mEstimatedCostToTarget = Double.MAX_VALUE;
			mEstimatedCostToTargetFromHere = Double.MAX_VALUE;
			mHashCode = computeHashCode();
		}

		private Item(final Item callItem, final SummaryItem summary) {
			mTargetState = summary.mReturnItem.mTargetState;
			mHierPreStates = new ElementHashedArrayDeque<>(callItem.mHierPreStates);
			mHierPreStates.pop();
			mLetter = summary.mReturnItem.mLetter;
			mBackPointer = new SummaryItem(callItem, summary);
			mItemType = ItemType.RETURN;

			mCostSoFar = -1.0;
			mEstimatedCostToTarget = Double.MAX_VALUE;
			mEstimatedCostToTargetFromHere = Double.MAX_VALUE;
			mHashCode = computeHashCode();
		}

		void setEstimatedCostToTarget(final double value) {
			mEstimatedCostToTargetFromHere = value;
			mEstimatedCostToTarget = mEstimatedCostToTargetFromHere + mCostSoFar;
		}

		void setCostSoFar(final double costSoFar) {
			mCostSoFar = costSoFar;
			assert checkCost(mCostSoFar, constructRun()) : "Cost is wrong";
		}

		@Override
		public int compareTo(final Item o) {
			return Double.compare(mEstimatedCostToTarget, o.mEstimatedCostToTarget);
		}

		public STATE getHierPreState() {
			return mHierPreStates.peek();
		}

		@Override
		public STATE getTargetState() {
			return mTargetState;
		}

		/**
		 * @return true iff the hierarchical pre states of this items are a prefix of the hierarchical pre states of the
		 *         other item, false otherwise.
		 */
		public boolean isHierStatesPrefixOf(final Item other) {
			final Iterator<STATE> iter = mHierPreStates.descendingIterator();
			final Iterator<STATE> otherIter = other.mHierPreStates.descendingIterator();
			while (iter.hasNext() && otherIter.hasNext()) {
				final STATE o1 = iter.next();
				final STATE o2 = otherIter.next();
				if (!(o1 == null ? o2 == null : o1.equals(o2))) {
					return false;
				}
			}
			return !iter.hasNext();
		}

		/**
		 * @return true iff the hierarchical pre states of this items are a prefix of the hierarchical pre states of the
		 *         other item ignoring the maxExtension items on top of this, false otherwise.
		 */
		public boolean isHierStatesPrefixOf(final Item other, int maxExtension) {
			final Iterator<STATE> iter = mHierPreStates.descendingIterator();
			final Iterator<STATE> otherIter = other.mHierPreStates.descendingIterator();
			while (iter.hasNext() && otherIter.hasNext()) {
				final STATE o1 = iter.next();
				final STATE o2 = otherIter.next();
				if (!(o1 == null ? o2 == null : o1.equals(o2))) {
					return false;
				}
			}

			if (iter.hasNext()) {
				// we have more items, but the other one does not, so we are not
				// a prefix
				return false;
			}
			// we are a prefix of other, but we are lenient for up to
			// maxExtension:
			while (otherIter.hasNext() && maxExtension > 0) {
				maxExtension--;
				otherIter.next();
			}
			return otherIter.hasNext() || maxExtension < 0;
		}

		/**
		 *
		 * @return true iff the last two hierarchical pre states of this item are equal to the last two hierarchical pre
		 *         states of the other item, false otherwise.
		 */
		public boolean isAncestorEqual(final Item other) {
			final Iterator<STATE> iter = mHierPreStates.iterator();
			final Iterator<STATE> otherIter = other.mHierPreStates.iterator();

			int i = 0;
			while (iter.hasNext() && otherIter.hasNext() && i < 2) {
				final STATE o1 = iter.next();
				final STATE o2 = otherIter.next();
				if (!(o1 == null ? o2 == null : o1.equals(o2))) {
					return false;
				}
				++i;
			}
			return i == 2;
		}

		public Item findCorrespondingCallItem() {
			if (mItemType != ItemType.RETURN) {
				return null;
			}
			IWithBackPointer<STATE> current = mBackPointer;

			final Deque<IWithBackPointer<STATE>> localStack = new ArrayDeque<>();
			while (current != null) {
				if (current.getClass() == getClass()) {
					final Item curr = (Item) current;
					if (curr.mItemType == ItemType.RETURN) {
						localStack.push(curr);
					} else if (curr.mItemType == ItemType.CALL) {
						if (localStack.isEmpty()) {
							return curr;
						}
						localStack.pop();
					}
				}
				current = current.getBackpointer();
			}
			return null;
		}

		public NestedRun<LETTER, STATE> constructRun() {
			return constructRun(Objects::isNull, false);
		}

		public NestedRun<LETTER, STATE> constructRun(final Predicate<IWithBackPointer<STATE>> until,
				final boolean keepBreakItem) {
			final List<IWithBackPointer<STATE>> runInItems = new ArrayList<>();
			IWithBackPointer<STATE> current = this;
			while (true) {
				runInItems.add(current);
				current = current.getBackpointer();
				if (until.test(current)) {
					if (keepBreakItem) {
						runInItems.add(current);
					}
					break;
				}
			}
			Collections.reverse(runInItems);

			final List<NestedRun<LETTER, STATE>> subruns = new ArrayList<>();
			List<Item> currentSubrun = new ArrayList<>();
			for (final IWithBackPointer<STATE> elem : runInItems) {
				if (elem.getClass() == getClass()) {
					currentSubrun.add((Item) elem);
				} else if (elem instanceof IsEmptyHeuristic.SummaryItem) {
					subruns.add(constructRunFromItems(currentSubrun));
					subruns.add(((SummaryItem) elem).mSubrun);
					currentSubrun = new ArrayList<>();
				}
			}
			if (!currentSubrun.isEmpty()) {
				subruns.add(constructRunFromItems(currentSubrun));
			}
			assert !subruns.isEmpty();
			final Iterator<NestedRun<LETTER, STATE>> iter = subruns.iterator();
			NestedRun<LETTER, STATE> run = null;
			while (iter.hasNext()) {
				if (run == null) {
					run = iter.next();
				} else {
					run = run.concatenate(iter.next());
				}

			}
			return run;
		}

		private NestedRun<LETTER, STATE> constructRunFromItems(final List<Item> runInItems) {
			if (runInItems.isEmpty()) {
				throw new IllegalArgumentException();
			}
			// construct nesting relation
			final ArrayList<STATE> stateSequence = new ArrayList<>();
			final Item firstItem = runInItems.get(0);
			stateSequence.add(firstItem.mTargetState);
			@SuppressWarnings("unchecked")
			final LETTER[] word = (LETTER[]) new Object[runInItems.size() - 1];
			return constructRunFromItemsWithoutInitialState(runInItems.subList(1, runInItems.size()), stateSequence,
					word);
		}

		private NestedRun<LETTER, STATE> constructRunFromItemsWithoutInitialState(final List<Item> runInItems,
				final ArrayList<STATE> stateSequence, final LETTER[] word) {
			final Deque<Integer> callIndices = new ArrayDeque<>();
			final int[] nestingRelation = new int[word.length];
			int i = 0;
			for (final Item item : runInItems) {
				word[i] = item.mLetter;
				stateSequence.add(item.mTargetState);
				switch (item.mItemType) {
				case CALL:
					callIndices.push(i);
					nestingRelation[i] = NestedWord.PLUS_INFINITY;
					break;
				case INTERNAL:
					nestingRelation[i] = NestedWord.INTERNAL_POSITION;
					break;
				case RETURN:
					if (callIndices.isEmpty()) {
						nestingRelation[i] = NestedWord.MINUS_INFINITY;
					} else {
						final int lastCall = callIndices.pop();
						nestingRelation[i] = lastCall;
						nestingRelation[lastCall] = i;
					}
					break;
				case INITIAL:
				default:
					throw new UnsupportedOperationException();
				}

				++i;
			}
			final NestedWord<LETTER> nestedWord = new NestedWord<>(word, nestingRelation);
			return new NestedRun<>(nestedWord, stateSequence);
		}

		@Override
		public int hashCode() {
			return mHashCode;
		}

		private int computeHashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + (mHierPreStates == null ? 0 : mHierPreStates.hashCode());
			result = prime * result + (mTargetState == null ? 0 : mTargetState.hashCode());
			result = prime * result + (mLetter == null ? 0 : mLetter.hashCode());
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			@SuppressWarnings("unchecked")
			final Item other = (Item) obj;
			if (mHierPreStates == null) {
				if (other.mHierPreStates != null) {
					return false;
				}
			} else if (!mHierPreStates.equals(other.mHierPreStates)) {
				return false;
			}
			if (mTargetState == null) {
				if (other.mTargetState != null) {
					return false;
				}
			} else if (!mTargetState.equals(other.mTargetState)) {
				return false;
			}
			if (mLetter == null) {
				if (other.mLetter != null) {
					return false;
				}
			} else if (!mLetter.equals(other.mLetter)) {
				return false;
			}
			return true;
		}

		@Override
		public String toString() {
			final Function<Object, String> toStr;
			if (DEBUG_MESSAGES_USE_HASHCODE) {
				toStr = a -> String.valueOf(a.hashCode());
			} else {
				toStr = Objects::toString;
			}

			final String hier = mHierPreStates.stream().map(toStr).collect(Collectors.joining(","));

			if (mCostSoFar == 0.0) {
				return String.format("%8s: {%s} T%s {%s}", mItemType, hier, mLetter == null ? 0 : toStr.apply(mLetter),
						toStr.apply(mTargetState));

			}

			final String ectt =
					mEstimatedCostToTarget == Double.MAX_VALUE ? "MAX" : String.valueOf(mEstimatedCostToTarget);
			final String ecttfh = mEstimatedCostToTargetFromHere == Double.MAX_VALUE ? "MAX"
					: String.valueOf(mEstimatedCostToTargetFromHere);

			return String.format("%8s: {%s} T%s {%s} (g=%f, h=%s, f=%s, s=%d)", mItemType, hier,
					mLetter == null ? 0 : toStr.apply(mLetter), toStr.apply(mTargetState), mCostSoFar, ecttfh, ectt,
					mHierPreStates.size());
		}

		@Override
		public IWithBackPointer<STATE> getBackpointer() {
			return mBackPointer;
		}

		public LETTER getLetter() {
			return mLetter;
		}

	}

	public enum AStarHeuristic {
		ZERO, RANDOM_HALF, RANDOM_FULL, SMT_FEATURE_COMPARISON, TESTCOMP
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 * @param <STATE>
	 *            Type of states
	 * @param <LETTER>
	 *            Type of transitions
	 */
	public interface IHeuristic<STATE, LETTER> {

		double getHeuristicValue(STATE state, STATE stateK, LETTER trans);

		double getConcreteCost(LETTER trans);

		public static <STATE, LETTER> IHeuristic<STATE, LETTER> getHeuristic(final AStarHeuristic astarHeuristic,
				final ScoringMethod scoringMethod, final long seed) {
			switch (astarHeuristic) {
			case RANDOM_FULL:
				return IHeuristic.getRandomHeuristicFull(seed);
			case RANDOM_HALF:
				return IHeuristic.getRandomHeuristicHalf(seed);
			case SMT_FEATURE_COMPARISON:
				return IHeuristic.getSmtFeatureHeuristic(scoringMethod);
			case ZERO:
				return IHeuristic.getZeroHeuristic();
			default:
				throw new UnsupportedOperationException("Unknown heuristic: " + astarHeuristic.toString());

			}
		}

		public static <STATE, LETTER> IHeuristic<STATE, LETTER> getHeuristic(final AStarHeuristic astarHeuristic,
				final ScoringMethod scoringMethod, final long seed, final Integer testGoalWithHighesID,
				final List<Integer> testGoalTodoStack) {
			switch (astarHeuristic) {

			case TESTCOMP:
				return IHeuristic.getTestCompHeuristic(testGoalWithHighesID, testGoalTodoStack);
			default:
				throw new UnsupportedOperationException("Unknown heuristic: " + astarHeuristic.toString());

			}
		}

		public static <STATE, LETTER> IHeuristic<STATE, LETTER> getZeroHeuristic() {
			return new IHeuristic<STATE, LETTER>() {
				@Override
				public final double getHeuristicValue(final STATE state, final STATE stateK, final LETTER trans) {
					return 0.0;
				}

				@Override
				public final double getConcreteCost(final LETTER e) {
					return 1.0;
				}
			};
		}

		public static <STATE, LETTER> IHeuristic<STATE, LETTER> getRandomHeuristicHalf(final long seed) {
			return new IHeuristic<STATE, LETTER>() {

				private final Random mRandom = new Random(seed);
				private final Map<LETTER, Double> mConcreteCosts = new HashMap<>();

				@Override
				public final double getHeuristicValue(final STATE state, final STATE stateK, final LETTER trans) {
					// normalize to [0.5 , 1.0]
					return 0.5 * mRandom.nextDouble() + 0.5;
				}

				@Override
				public final double getConcreteCost(final LETTER e) {
					return mConcreteCosts.computeIfAbsent(e, a -> 0.5 * mRandom.nextDouble() + 0.5);
				}
			};
		}

		public static <STATE, LETTER> IHeuristic<STATE, LETTER> getRandomHeuristicFull(final long seed) {
			return new IHeuristic<STATE, LETTER>() {

				private final Random mRandom = new Random(seed);
				private final Map<LETTER, Double> mConcreteCosts = new HashMap<>();

				@Override
				public final double getHeuristicValue(final STATE state, final STATE stateK, final LETTER trans) {
					return mRandom.nextDouble();
				}

				@Override
				public final double getConcreteCost(final LETTER e) {
					return mConcreteCosts.computeIfAbsent(e, a -> 0.1 + mRandom.nextDouble());
				}
			};
		}

		public static <STATE, LETTER> SmtFeatureHeuristic<STATE, LETTER>
				getSmtFeatureHeuristic(final ScoringMethod scoringMethod) {
			return new SmtFeatureHeuristic<>(scoringMethod);
		}

		public static <STATE, LETTER> TestCompHeuristic<STATE, LETTER>
				getTestCompHeuristic(final Integer testGoalWithHighesID, final List<Integer> testGoalTodoStack) {
			return new TestCompHeuristic<>(testGoalWithHighesID, testGoalTodoStack);
		}

	}

	/**
	 * An {@link ArrayDeque} that uses {@link #hashCode()} and {@link #equals(Object)} of an {@link AbstractList}.
	 *
	 * This means that two queues with the same elements in the same order are equal and have the same hashcode.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 * @param <E>
	 */
	private static final class ElementHashedArrayDeque<E> extends ArrayDeque<E> {
		private static final long serialVersionUID = 1L;

		public ElementHashedArrayDeque() {
			super();
		}

		public ElementHashedArrayDeque(final Collection<? extends E> c) {
			super(c);
		}

		@Override
		public int hashCode() {
			int hashCode = 1;
			for (final E e : this) {
				hashCode = 31 * hashCode + (e == null ? 0 : e.hashCode());
			}
			return hashCode;
		}

		@Override
		public boolean equals(final Object o) {
			if (o == this) {
				return true;
			}
			if (!(o instanceof ElementHashedArrayDeque)) {
				return false;
			}

			final Iterator<E> e1 = iterator();
			final Iterator<?> e2 = ((ElementHashedArrayDeque<?>) o).iterator();
			while (e1.hasNext() && e2.hasNext()) {
				final E o1 = e1.next();
				final Object o2 = e2.next();
				if (!(o1 == null ? o2 == null : o1.equals(o2))) {
					return false;
				}
			}
			return !(e1.hasNext() || e2.hasNext());
		}
	}
}
