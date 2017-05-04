/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval.UpDownEntry;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * TODO Documentation
 * <p>
 * TODO: Optimization: For most operations the internal and call successors of (<i>down</i>,<i>up</i>) are the same for
 * all down states. So a lot of successors are computed several times, but you could see the already in mTraversedNwa.
 * Suggestion: Extension that implements visitAndGetInternalSuccessors(DoubleDecker) and has abstract
 * constructInternalSuccessors(IState) method.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class DoubleDeckerVisitor<LETTER, STATE> {
	protected final AutomataLibraryServices mServices;
	protected final ILogger mLogger;

	/**
	 * Status whether a state reaches a final state.
	 * <p>
	 * This is used for optimization reasons.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	public enum ReachFinal {
		/**
		 * Whether an accepting state is reachable is unknown.
		 */
		UNKNOWN,
		/**
		 * An accepting state can be reached at least once.
		 */
		AT_LEAST_ONCE
	}

	protected INestedWordAutomaton<LETTER, STATE> mTraversedNwa;

	/**
	 * We remove afterwards all dead ends iff set to true.
	 */
	protected boolean mRemoveDeadEnds;

	/**
	 * We remove afterwards all non-live states iff set to true.
	 */
	protected boolean mRemoveNonLiveStates;

	/**
	 * Compute the predecessors of all DoubleDeckers. Neccessary for removal of dead ends. TODO: Optimization make this
	 * optional for cases where we don't want to minimize.
	 */
	protected boolean mComputePredecessorDoubleDeckers = true;

	/*
	/**
	 * Predecessor DoubleDeckers under internal transitions.
	 * Used only for removal of dead ends and non-live states.
	 * protected Map<DoubleDecker<STATE>, Set<DoubleDecker<STATE>>> mInternalPredecessors = new HashMap<>();
	 * /**
	 * Predecessor DoubleDeckers under summary transitions.
	 * Used only for removal of dead ends and non-live states.
	 * protected Map<DoubleDecker<STATE>, Set<DoubleDecker<STATE>>> mSummaryPredecessors = new HashMap<>();
	 * /**
	 * Predecessor DoubleDeckers under call transitions.
	 * Used only for removal of dead ends and non-live states.
	 * protected Map<DoubleDecker<STATE>, Set<DoubleDecker<STATE>>> mCallPredecessors = new HashMap<>();
	 * /**
	 * Predecessor DoubleDeckers under call transitions.
	 * Used only for removal of dead ends and non-live states.
	 * protected Map<DoubleDecker<STATE>, Set<DoubleDecker<STATE>>> mReturnPredecessors = new HashMap<>();
	 * /**
	 * DoubleDeckers that have been constructed but do not occur in any
	 * accepting run of the automaton.
	 * private Map<STATE, Set<STATE>> mRemovedDoubleDeckers = new HashMap<>();
	 * /**
	 * DoubleDeckers which occur on an accepting run.
	 * protected Set<DoubleDecker<STATE>> doubleDeckersThatCanReachFinal;
	 * protected Map<STATE, STATE> mCallSuccOfRemovedDown;
	 * protected DoubleDecker<STATE> auxiliaryEmptyStackDoubleDecker;
	 */

	/**
	 * We call a DoubleDecker marked if it has been visited or is contained in the worklist. The DoubleDecker
	 * (<i>down</i>,<i>up</i>) is marked iff <i>down</i> is contained in the range of <i>up</i>.
	 */
	private final Map<STATE, Map<STATE, ReachFinal>> mMarkedUp2Down = new HashMap<>();

	/**
	 * DoubleDecker that are already known but have not yet been visited.
	 */
	private final List<DoubleDecker<STATE>> mWorklist = new LinkedList<>();

	/**
	 * Pairs of states (q,q') of the automaton such that q' is reachable from q via a well-matched nested word in which
	 * the first position is a call position and the last position is a return position.
	 */
	private final Map<STATE, Map<STATE, STATE>> mCallReturnSummary = new HashMap<>();

	private long mDeadEndRemovalTime;

	private Set<STATE> mDeadEnds;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 */
	public DoubleDeckerVisitor(final AutomataLibraryServices services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
	}

	public Object getResult() {
		return mTraversedNwa;
	}

	/**
	 * True iff the DoubleDecker doubleDecker has been marked. A DoubleDecker is marked iff it has been visited or is in
	 * the mWorklist.
	 */
	private final boolean wasMarked(final DoubleDecker<STATE> doubleDecker) {
		final Map<STATE, ReachFinal> downState = mMarkedUp2Down.get(doubleDecker.getUp());
		if (downState == null) {
			return false;
		}
		return downState.containsKey(doubleDecker.getDown());
	}

	private final void mark(final DoubleDecker<STATE> doubleDecker) {
		Map<STATE, ReachFinal> downStates = mMarkedUp2Down.get(doubleDecker.getUp());
		if (downStates == null) {
			downStates = new HashMap<>();
			mMarkedUp2Down.put(doubleDecker.getUp(), downStates);
		}
		downStates.put(doubleDecker.getDown(), ReachFinal.UNKNOWN);

		/*
		Set<STATE> upStates = mMarked_Down2Up.get(doubleDecker.getDown());
		if (upStates == null) {
			upStates = new HashSet<STATE>();
			mMarked_Down2Up.put(doubleDecker.getDown(), upStates);
		}
		upStates.add(doubleDecker.getUp());
		*/
	}

	/**
	 * Add doubleDecker to worklist if it has not yet been marked.
	 */
	private final void enqueueAndMark(final DoubleDecker<STATE> doubleDecker) {
		if (!wasMarked(doubleDecker)) {
			mark(doubleDecker);
			mWorklist.add(doubleDecker);
		}
	}

	/*
	/**
	 * Record in predecessorMapping that preDoubleDecker is a predecessor of
	 * doubleDecker.
	 * predecessorMapping should be the mapping for either, call predecessors,
	 * internal predecessors, summary predecessors or return predecesssors.
	 */
	/*
	private final void memorizePredecessor(
		DoubleDecker<STATE> doubleDecker,
		DoubleDecker<STATE> preDoubleDecker,
		Map<DoubleDecker<STATE>, Set<DoubleDecker<STATE>>> predecessorMapping) {
	if (!mComputePredecessorDoubleDeckers) {
		return;
	}
	assert (predecessorMapping == mCallPredecessors
			|| predecessorMapping == mReturnPredecessors
			|| predecessorMapping == mInternalPredecessors
			|| predecessorMapping == mSummaryPredecessors);
	if (preDoubleDecker != null) {
		Set<DoubleDecker<STATE>> predSet = predecessorMapping.get(doubleDecker);
		if (predSet == null) {
			predSet = new HashSet<DoubleDecker<STATE>>();
			predecessorMapping.put(doubleDecker, predSet);
		}
		predSet.add(preDoubleDecker);
	}
	}
	*/

	/**
	 * Record that summarySucc is reachable from summaryPred via a run over a well-matched NestedWord.
	 */
	private final void addSummary(final STATE summaryPred, final STATE summarySucc, final STATE returnPred) {
		Map<STATE, STATE> summarySuccessors = mCallReturnSummary.get(summaryPred);
		if (summarySuccessors == null) {
			summarySuccessors = new HashMap<>();
			mCallReturnSummary.put(summaryPred, summarySuccessors);
		}
		summarySuccessors.put(summarySucc, returnPred);
		enqueueSummarySuccs(summaryPred, summarySucc, returnPred);
	}

	/**
	 * For all DoubleDeckers (<i>down</i>,summaryPred) that have been marked enqueue and mark the DoubleDecker
	 * (<i>down</i>,summarySucc) and record that the DoubleDecker (summaryPred,returnPred) is a predecessor of
	 * (<i>down</i>,summarySucc).
	 */
	private final void enqueueSummarySuccs(final STATE summaryPred, final STATE summarySucc, final STATE returnPred) {
		for (final STATE summaryPreDown : mMarkedUp2Down.get(summaryPred).keySet()) {
			final DoubleDecker<STATE> summarySuccDoubleDecker = new DoubleDecker<>(summaryPreDown, summarySucc);
			/*
			final DoubleDecker<STATE> doubleDecker = new DoubleDecker<>(summaryPreDown, summaryPred);
			final DoubleDecker<STATE> summaryReturnPred = new DoubleDecker<>(summaryPred, returnPred);
			memorizePredecessor(summarySuccDoubleDecker, summaryReturnPred, mReturnPredecessors);
			memorizePredecessor(summarySuccDoubleDecker, doubleDecker, mSummaryPredecessors);
			*/
			enqueueAndMark(summarySuccDoubleDecker);
		}
	}

	/**
	 * Get all states <i>down</i> such that the DoubleDecker (<i>down</i>,<i>up</i>) has been visited so far.
	 */
	private final Set<STATE> getKnownDownStates(final STATE upState) {
		final Set<STATE> downStates = mMarkedUp2Down.get(upState).keySet();
		if (downStates == null) {
			return new HashSet<>(0);
		}
		return downStates;
	}

	public Map<STATE, Map<STATE, ReachFinal>> getUp2DownMapping() {
		return Collections.unmodifiableMap(mMarkedUp2Down);
	}

	protected final void traverseDoubleDeckerGraph() throws AutomataOperationCanceledException {
		final Collection<STATE> initialStates = getInitialStates();
		for (final STATE state : initialStates) {
			final DoubleDecker<STATE> initialDoubleDecker =
					new DoubleDecker<>(mTraversedNwa.getEmptyStackState(), state);
			enqueueAndMark(initialDoubleDecker);
		}

		while (!mWorklist.isEmpty()) {
			final DoubleDecker<STATE> doubleDecker = mWorklist.remove(0);

			final Iterable<STATE> internalSuccs = visitAndGetInternalSuccessors(doubleDecker);
			for (final STATE succ : internalSuccs) {
				final DoubleDecker<STATE> succDoubleDecker = new DoubleDecker<>(doubleDecker.getDown(), succ);
				// memorizePredecessor(succDoubleDecker, doubleDecker, mInternalPredecessors);
				enqueueAndMark(succDoubleDecker);
			}
			final Iterable<STATE> callSuccs = visitAndGetCallSuccessors(doubleDecker);
			for (final STATE succ : callSuccs) {
				final DoubleDecker<STATE> succDoubleDecker = new DoubleDecker<>(doubleDecker.getUp(), succ);
				// memorizePredecessor(succDoubleDecker, doubleDecker, mCallPredecessors);
				enqueueAndMark(succDoubleDecker);
			}
			final Iterable<STATE> returnSuccs = visitAndGetReturnSuccessors(doubleDecker);
			for (final STATE succ : returnSuccs) {
				addSummary(doubleDecker.getDown(), succ, doubleDecker.getUp());
				for (final STATE resLinPredCallerState : getKnownDownStates(doubleDecker.getDown())) {
					final DoubleDecker<STATE> succDoubleDecker = new DoubleDecker<>(resLinPredCallerState, succ);
					// memorizePredecessor(succDoubleDecker, doubleDecker, mReturnPredecessors);
					enqueueAndMark(succDoubleDecker);
				}
			}

			if (mCallReturnSummary.containsKey(doubleDecker.getUp())) {
				final Map<STATE, STATE> summarySucc2returnPred = mCallReturnSummary.get(doubleDecker.getUp());
				for (final Entry<STATE, STATE> entry : summarySucc2returnPred.entrySet()) {
					final STATE summarySucc = entry.getKey();
					final DoubleDecker<STATE> summarySuccDoubleDecker =
							new DoubleDecker<>(doubleDecker.getDown(), summarySucc);
					// final STATE returnPred = entry.getValue();
					// final DoubleDecker<STATE> shortcutReturnPred =
					// 		new DoubleDecker<>(doubleDecker.getUp(), returnPred);
					// memorizePredecessor(summarySuccDoubleDecker, shortcutReturnPred, mReturnPredecessors);
					// memorizePredecessor(summarySuccDoubleDecker, doubleDecker, mSummaryPredecessors);
					enqueueAndMark(summarySuccDoubleDecker);
				}
			}
			if (mServices.getProgressAwareTimer() != null && !mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}

		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Before removal of dead ends " + mTraversedNwa.sizeInformation());
		}
		if (mRemoveDeadEnds && mRemoveNonLiveStates) {
			throw new IllegalArgumentException("RemoveDeadEnds and RemoveNonLiveStates is set");
		}

		mDeadEnds = computeDeadEnds();

		/*
		final Set<DoubleDecker<STATE>> oldMethod = removedDoubleDeckersOldMethod();
		final Set<DoubleDecker<STATE>> newMethod = removedDoubleDeckersViaIterator();
		assert oldMethod.containsAll(newMethod);
		assert newMethod.containsAll(oldMethod);
		*/

		if (mRemoveDeadEnds) {
			// new TestFileWriter(mTraversedNwa, "TheAutomaotn", TestFileWriter.Labeling.TOSTRING);
			removeDeadEnds();
			if (mTraversedNwa.getInitialStates().isEmpty()) {
				assert mTraversedNwa.getStates().isEmpty();
			}
			if (mLogger.isInfoEnabled()) {
				mLogger.info("After removal of dead ends " + mTraversedNwa.sizeInformation());
			}

		}
		if (mRemoveNonLiveStates) {
			// mLogger.warn("Minimize before non-live removal: " +
			// 		((NestedWordAutomaton<LETTER, STATE>) (new MinimizeDfa<LETTER, STATE>(mTraversedNwa)).getResult())
			// 				.sizeInformation());
			removeNonLiveStates();
			// mLogger.warn("Minimize after non-live removal: " +
			// 		((NestedWordAutomaton<LETTER, STATE>) (new MinimizeDfa<LETTER, STATE>(mTraversedNwa)).getResult())
			// 				.sizeInformation());
			if (mTraversedNwa.getInitialStates().isEmpty()) {
				assert mTraversedNwa.getStates().isEmpty();
				// mTraversedNwa = getTotalizedEmptyAutomaton();
			}
			if (mLogger.isInfoEnabled()) {
				mLogger.info("After removal of nonLiveStates " + mTraversedNwa.sizeInformation());
			}
		}
	}

	/*
	protected NestedWordAutomaton<LETTER, STATE> getTotalizedEmptyAutomaton() {
		NestedWordAutomaton<LETTER, STATE> emptyAutomaton = new NestedWordAutomaton<LETTER, STATE>(
				mTraversedNwa.getInternalAlphabet(),
				mTraversedNwa.getCallAlphabet(),
				mTraversedNwa.getReturnAlphabet(),
				mTraversedNwa.getStateFactory());
		STATE sinkState =
				emptyAutomaton.getStateFactory().createSinkStateContent();
		emptyAutomaton.addState(true, false, sinkState);
		
		for (STATE state : emptyAutomaton.getStates()) {
			for (LETTER letter : emptyAutomaton.getInternalAlphabet()) {
				if (emptyAutomaton.succInternal(state, letter).isEmpty()) {
					emptyAutomaton.addInternalTransition(state, letter, sinkState);
				}
			}
			for (LETTER letter : emptyAutomaton.getCallAlphabet()) {
				if (emptyAutomaton.succCall(state, letter).isEmpty()) {
					emptyAutomaton.addCallTransition(state, letter, sinkState);
				}
			}
			for (LETTER symbol : emptyAutomaton.getReturnAlphabet()) {
				for (STATE hier : emptyAutomaton.getStates()) {
					if (emptyAutomaton.succReturn(state, hier, symbol).isEmpty()) {
						emptyAutomaton.addReturnTransition(state, hier, symbol, sinkState);
					}
				}
			}
		}
		return emptyAutomaton;
	}
	*/

	/**
	 * @return Initial states of automaton.
	 */
	protected abstract Collection<STATE> getInitialStates();

	/**
	 * @return Internal successors of doubleDeckers up state.
	 */
	protected abstract Collection<STATE> visitAndGetInternalSuccessors(DoubleDecker<STATE> doubleDecker);

	/**
	 * @return Call successors of doubleDeckers up state.
	 */
	protected abstract Collection<STATE> visitAndGetCallSuccessors(DoubleDecker<STATE> doubleDecker);

	/**
	 * @return Return successors of doubleDeckers up state.
	 */
	protected abstract Collection<STATE> visitAndGetReturnSuccessors(DoubleDecker<STATE> doubleDecker);

	private void enqueueInternalPred(final STATE upState, final Collection<STATE> downStates,
			final DoubleDeckerWorkList worklist) {
		for (final IncomingInternalTransition<LETTER, STATE> inTrans : mTraversedNwa.internalPredecessors(upState)) {
			final STATE predUp = inTrans.getPred();
			for (final STATE down : downStates) {
				final ReachFinal doubleDeckerReach = mMarkedUp2Down.get(predUp).get(down);
				if (doubleDeckerReach == ReachFinal.UNKNOWN) {
					// assert (doubleDeckersThatCanReachFinal
					// 		.contains(new DoubleDecker<STATE>(down, predUp))) : "deadEndRemovalFailed";
					worklist.add(predUp, down);
				} else {
					assert doubleDeckerReach == null || doubleDeckerReach == ReachFinal.AT_LEAST_ONCE;
				}
			}
		}
	}

	private void enqueueCallPred(final STATE upState, final Collection<STATE> downStates,
			final DoubleDeckerWorkList worklist) {
		// we for call transitions we may use all of predecessors
		// down states (use only when considering only non ret ancestors!)
		for (final IncomingCallTransition<LETTER, STATE> inTrans : mTraversedNwa.callPredecessors(upState)) {
			final STATE predUp = inTrans.getPred();
			for (final STATE predDown : mMarkedUp2Down.get(predUp).keySet()) {
				final ReachFinal doubleDeckerReach = mMarkedUp2Down.get(predUp).get(predDown);
				if (doubleDeckerReach == ReachFinal.UNKNOWN) {
					// assert (doubleDeckersThatCanReachFinal
					// 		.contains(new DoubleDecker<STATE>(predDown, predUp))) : "deadEndRemovalFailed";
					worklist.add(predUp, predDown);
				} else {
					assert doubleDeckerReach == null || doubleDeckerReach == ReachFinal.AT_LEAST_ONCE;
				}
			}
		}
	}

	private void enqueueReturnPred(final STATE upState, final Collection<STATE> downStates,
			final DoubleDeckerWorkList summaryWorklist, final DoubleDeckerWorkList linPredworklist) {
		for (final IncomingReturnTransition<LETTER, STATE> inTrans : mTraversedNwa.returnPredecessors(upState)) {
			final STATE hier = inTrans.getHierPred();
			// We have to check if there is some double decker (hier,down) with
			// down∈downStates. Only in that case we may add (lin,hier) to the
			// worklist (done after this while loop)
			boolean hierIsUpOfSomePredDoubleDecker = false;
			for (final STATE down : downStates) {
				final ReachFinal doubleDeckerReach = mMarkedUp2Down.get(hier).get(down);
				if (doubleDeckerReach == null) {
					continue;
				}
				hierIsUpOfSomePredDoubleDecker = true;
				if (doubleDeckerReach == ReachFinal.UNKNOWN) {
					// assert (doubleDeckersThatCanReachFinal
					// 		.contains(new DoubleDecker<STATE>(down, hier))) : "deadEndRemovalFailed";
					summaryWorklist.add(hier, down);
				} else {
					assert doubleDeckerReach == ReachFinal.AT_LEAST_ONCE;
				}
			}
			final STATE linPred = inTrans.getLinPred();
			if (hierIsUpOfSomePredDoubleDecker) {
				final ReachFinal doubleDeckerReach = mMarkedUp2Down.get(linPred).get(hier);
				if (doubleDeckerReach == ReachFinal.UNKNOWN) {
					// assert (doubleDeckersThatCanReachFinal
					// 		.contains(new DoubleDecker<STATE>(hier, linPred))) : "deadEndRemovalFailed";
					linPredworklist.add(linPred, hier);
				} else {
					assert doubleDeckerReach == ReachFinal.AT_LEAST_ONCE;
				}
			}
		}
	}

	private final Set<STATE> computeDeadEnds() {
		// Set used to compute the states that can never reach the final state
		// initialized with all states and narrowed by the algorithm
		final Set<STATE> statesNeverReachFinal = new HashSet<>(mTraversedNwa.getStates());

		final DoubleDeckerWorkList nonRetAncest = new DoubleDeckerWorkList();

		final DoubleDeckerWorkList allAncest = new DoubleDeckerWorkList();

		// compute return ancestors in two steps

		// step one: consider only hierarchical predecessors of return
		// transitions. Reason: We want to compute all reachable double
		// deckers. Neglecting linPreds of return transitions all double
		// deckers (up,down) of an up state are reachable.
		for (final STATE state : mTraversedNwa.getFinalStates()) {
			final Map<STATE, ReachFinal> down2reachFinal = mMarkedUp2Down.get(state);
			if (down2reachFinal == null) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Unreachable final state: " + state);
				}
			} else {
				for (final STATE down : mMarkedUp2Down.get(state).keySet()) {
					nonRetAncest.add(state, down);
				}
			}
		}
		while (!nonRetAncest.isEmpty()) {
			final Map<STATE, Set<STATE>> up2downs = nonRetAncest.removeUpAndItsDowns();
			assert up2downs.size() == 1;
			final STATE up = up2downs.keySet().iterator().next();
			statesNeverReachFinal.remove(up);
			final Set<STATE> downs = up2downs.get(up);
			// down states such that final reachability of (up,down) was new
			// information (and has to be propagated to predecessors.
			final List<STATE> updatedDowns = new ArrayList<>();
			for (final STATE down : downs) {
				if (mMarkedUp2Down.get(up).get(down) == ReachFinal.UNKNOWN) {
					updatedDowns.add(down);
				} else {
					assert mMarkedUp2Down.get(up).get(down) == ReachFinal.AT_LEAST_ONCE;
				}
				/*
				assert (doubleDeckersThatCanReachFinal.contains(new DoubleDecker<>(down, up))) : "deadEndRemovalFailed";
				*/
				mMarkedUp2Down.get(up).put(down, ReachFinal.AT_LEAST_ONCE);
			}

			if (!updatedDowns.isEmpty()) {
				enqueueInternalPred(up, updatedDowns, nonRetAncest);

				enqueueCallPred(up, updatedDowns, nonRetAncest);
				enqueueReturnPred(up, updatedDowns, nonRetAncest, allAncest);
			}
		}

		// step two
		while (!allAncest.isEmpty()) {
			final Map<STATE, Set<STATE>> up2downs = allAncest.removeUpAndItsDowns();
			assert up2downs.size() == 1;
			final STATE up = up2downs.keySet().iterator().next();
			statesNeverReachFinal.remove(up);
			final Set<STATE> downs = up2downs.get(up);
			// down states such that final reachability of (up,down) was new
			// information (and has to be propagated to predecessors.
			final List<STATE> updatedDowns = new ArrayList<>();
			for (final STATE down : downs) {
				if (mMarkedUp2Down.get(up).get(down) == ReachFinal.UNKNOWN) {
					updatedDowns.add(down);
				}
				/*
				assert (doubleDeckersThatCanReachFinal.contains(new DoubleDecker<>(down, up))) : "deadEndRemovalFailed";
				*/
				mMarkedUp2Down.get(up).put(down, ReachFinal.AT_LEAST_ONCE);
			}
			if (!updatedDowns.isEmpty()) {
				enqueueInternalPred(up, updatedDowns, allAncest);
				// we may omit call transitions - state are already
				// considered as hier preds of returns.
				enqueueReturnPred(up, updatedDowns, allAncest, allAncest);
			}
		}
		return statesNeverReachFinal;
	}

	/*
	private final Set<STATE> computeStatesThatCanNotReachFinal() {
	
	 // // Set used to compute the states that can never reach the final state
	 // // initialized with all states and narrowed by the algorithm
	 // Set<STATE> statesNeverReachFinal = new
	 HashSet<STATE>(mTraversedNwa.getStates());
	 //
	 // {
	 // Set<DoubleDecker<STATE>> nonReturnAncestors = new
	 HashSet<DoubleDecker<STATE>>();
	 // Set<DoubleDecker<STATE>> acceptingDoubleDeckers = new
	 HashSet<DoubleDecker<STATE>>();
	 // for (STATE finalState : mTraversedNwa.getFinalStates()) {
	 // Set<STATE> finalsDownStates =
	 mMarked_Up2Down.get(finalState).keySet();
	 // for (STATE downStatesOfFinal : finalsDownStates) {
	 // DoubleDecker<STATE> summary = new
	 DoubleDecker<STATE>(downStatesOfFinal, finalState);
	 // acceptingDoubleDeckers.add(summary);
	 // }
	 // }
	 //
	 // LinkedList<DoubleDecker<STATE>> ancestorSearchWorklist;
	 //
	 // //Computation of nonReturnAncestors
	 // ancestorSearchWorklist = new LinkedList<DoubleDecker<STATE>>();
	 // ancestorSearchWorklist.addAll(acceptingDoubleDeckers);
	 // nonReturnAncestors.addAll(acceptingDoubleDeckers);
	 // while (!ancestorSearchWorklist.isEmpty()) {
	 // DoubleDecker<STATE> doubleDecker=
	 ancestorSearchWorklist.removeFirst();
	 // statesNeverReachFinal.remove(doubleDecker.getUp());
	 // ArrayList<Set<DoubleDecker<STATE>>> predSets = new
	 ArrayList<Set<DoubleDecker<STATE>>>(3);
	 // predSets.add(mInternalPredecessors.get(doubleDecker));
	 // predSets.add(mSummaryPredecessors.get(doubleDecker));
	 // predSets.add(mCallPredecessors.get(doubleDecker));
	 // for (Set<DoubleDecker<STATE>> preds : predSets) {
	 // if (preds == null) {
	 // //assert mTraversedNwa.getInitial().contains(doubleDecker.getUp());
	 // }
	 // else {
	 // for (DoubleDecker<STATE> pred : preds) {
	 // if (!nonReturnAncestors.contains(pred)) {
	 // nonReturnAncestors.add(pred);
	 // ancestorSearchWorklist.add(pred);
	 // }
	 // }
	 // }
	 // }
	 // }
	 //
	 // //add Return Ancestors
	 // ancestorSearchWorklist = new LinkedList<DoubleDecker<STATE>>();
	 // ancestorSearchWorklist.addAll(nonReturnAncestors);
	 // while (!ancestorSearchWorklist.isEmpty()) {
	 // DoubleDecker<STATE> doubleDecker=
	 ancestorSearchWorklist.removeFirst();
	 // statesNeverReachFinal.remove(doubleDecker.getUp());
	 // ArrayList<Set<DoubleDecker<STATE>>> predSets = new
	 ArrayList<Set<DoubleDecker<STATE>>>(3);
	 // predSets.add(mInternalPredecessors.get(doubleDecker));
	 // predSets.add(mSummaryPredecessors.get(doubleDecker));
	 // predSets.add(mReturnPredecessors.get(doubleDecker));
	 // for (Set<DoubleDecker<STATE>> preds : predSets) {
	 // if (preds == null) {
	 // //assert mTraversedNwa.getInitial().contains(doubleDecker.getUp());
	 // }
	 // else {
	 // for (DoubleDecker<STATE> pred : preds) {
	 // if (!nonReturnAncestors.contains(pred)) {
	 // nonReturnAncestors.add(pred);
	 // ancestorSearchWorklist.add(pred);
	 // }
	 // }
	 // }
	 // }
	 // }
	 //
	 // // DoubleDeckers that have been visited in this search which starts
	 from
	 // // final states
	 // doubleDeckersThatCanReachFinal = nonReturnAncestors;
	 // doubleDeckersThatCanReachFinal.addAll(acceptingDoubleDeckers);
	 // }
	
	 Set<STATE> statesNeverReachFin =
	 computeStatesThatCanNotReachFinalNewVersion();
	 // mLogger.error("STATEs " + mTraversedNwa.getStates().size());
	 //// new TestFileWriter(mTraversedNwa, "TheAutomaotn",
	 TestFileWriter.Labeling.TOSTRING, "test");
	 // assert statesNeverReachFinal.containsAll(statesNeverReachFin) :
	 "deadEndRemovalFailed";
	 // assert statesNeverReachFin.containsAll(statesNeverReachFinal) :
	 "deadEndRemovalFailed";
	 //
	 // for (DoubleDecker<STATE> dd : doubleDeckersThatCanReachFinal) {
	 // STATE up = dd.getUp();
	 // STATE down = dd.getDown();
	 // assert mMarked_Up2Down.get(up).get(down) == ReachFinal.AT_LEAST_ONCE
	 : "deadEndRemovalFailed";
	 // }
	 // for (STATE up : mMarked_Up2Down.keySet()) {
	 // for (STATE down : mMarked_Up2Down.get(up).keySet()) {
	 // if (mMarked_Up2Down.get(up).get(down) == ReachFinal.AT_LEAST_ONCE &&
	 down != mTraversedNwa.getEmptyStackState()) {
	 // assert (doubleDeckersThatCanReachFinal.contains(new
	 DoubleDecker<STATE>(down, up))) : "deadEndRemovalFailed";
	 // }
	 // }
	 // }
	
	 return statesNeverReachFin;
	 }
	*/

	/**
	 * Remove in the resulting automaton all states that can not reach a final state.
	 * 
	 * @param computeRemovedDoubleDeckersAndCallSuccessors
	 *            compute the set of all DoubleDeckers which occurred in the build automaton but are not reachable after
	 *            the removal TODO non-existent parameter
	 * @return true iff at least one state was removed.
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public final boolean removeDeadEnds() throws AutomataOperationCanceledException {
		@SuppressWarnings("squid:S1941")
		final long startTime = System.currentTimeMillis();

		// some states are not removed but lose initial property
		final Set<STATE> statesThatShouldNotBeInitialAnyMore = new HashSet<>();
		for (final STATE state : mTraversedNwa.getInitialStates()) {
			if (mDeadEnds.contains(state)) {
				continue;
			}
			if (mMarkedUp2Down.get(state).get(mTraversedNwa.getEmptyStackState()) == ReachFinal.AT_LEAST_ONCE) {
				continue;
			}
			assert mMarkedUp2Down.get(state).get(mTraversedNwa.getEmptyStackState()) == ReachFinal.UNKNOWN;
			statesThatShouldNotBeInitialAnyMore.add(state);
		}
		for (final STATE state : statesThatShouldNotBeInitialAnyMore) {
			((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).makeStateNonIntial(state);
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("The following state is not final any more: " + state);
			}
		}

		for (final STATE state : mDeadEnds) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
			((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).removeState(state);
		}

		final boolean atLeastOneStateRemoved = !mDeadEnds.isEmpty();
		mDeadEnds = null;
		mDeadEndRemovalTime += (System.currentTimeMillis() - startTime);
		if (mLogger.isInfoEnabled()) {
			mLogger.info("After removal of dead ends " + mTraversedNwa.sizeInformation());
		}
		return atLeastOneStateRemoved;
	}

	/*
	/**
	 * Announce removal of all DoubleDeckers (<i>down</i>,<i>up</i>) such that
	 * <i>down</i> or <i>up</i> is contained in statesGoingToBeRemoved.
	 */
	// _before_ because on removal we want to be able to access all states of the automaton
	/*
	private void announceRemovalOfDoubleDeckers(final Set<STATE> statesGoingToBeRemoved) {
		mCallSuccOfRemovedDown = new HashMap<STATE, STATE>();
		
		/**
		 * DoubleDeckers that have been constructed but do not occur in any
		 * accepting run of the automaton.
		 */
	/*
	for (final STATE up : mMarked_Up2Down.keySet()) {
		for (final STATE down : mMarked_Up2Down.get(up).keySet()) {
			if (mMarked_Up2Down.get(up).get(down) == ReachFinal.UNKNOWN) {
				
				Set<STATE> downStates = mRemovedDoubleDeckers.get(up);
				if (downStates == null) {
					downStates = new HashSet<>();
					mRemovedDoubleDeckers.put(up, downStates);
				}
				downStates.add(down);
				
				final Set<STATE> downCallSuccs = computeState2CallSuccs(down);
				if (downCallSuccs.size() > 1) {
					throw new UnsupportedOperationException("If state has" +
							" several outgoing call transitions Hoare annotation might be incorrect.");
				} else if (downCallSuccs.size() == 1) {
					final STATE callSucc = downCallSuccs.iterator().next();
					mCallSuccOfRemovedDown.put(down, callSucc);
				} else {
					assert downCallSuccs.isEmpty();
				}
			}
		}
	}
	}
	*/

	/**
	 * Compute call successors for a given set of states.
	 */
	@SuppressWarnings("squid:S1698")
	private Set<STATE> computeState2CallSuccs(final STATE state) {
		final Set<STATE> callSuccs = new HashSet<>();
		// equality intended here
		if (state != mTraversedNwa.getEmptyStackState()) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : mTraversedNwa.callSuccessors(state)) {
				callSuccs.add(trans.getSucc());
			}
		}
		return callSuccs;
	}

	/**
	 * @return true iff state has successors.
	 */
	private boolean hasSuccessors(final STATE state) {
		if (mTraversedNwa.internalSuccessors(state).iterator().hasNext()) {
			return true;
		}
		if (mTraversedNwa.callSuccessors(state).iterator().hasNext()) {
			return true;
		}
		if (mTraversedNwa.returnSuccessors(state).iterator().hasNext()) {
			return true;
		}
		return false;
	}

	/**
	 * Remove all state that are accepting and do not have any successor.
	 * 
	 * @return true iff some state was removed
	 */
	private final boolean removeAcceptingStatesWithoutSuccessors() {

		final ArrayList<STATE> finalStatesWithoutSuccessor = new ArrayList<>();
		for (final STATE accepting : mTraversedNwa.getFinalStates()) {
			if (!hasSuccessors(accepting)) {
				finalStatesWithoutSuccessor.add(accepting);
			}
		}
		final boolean atLeastOneStateRemoved = !finalStatesWithoutSuccessor.isEmpty();
		for (final STATE finalStateWithoutSuccessor : finalStatesWithoutSuccessor) {
			((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).removeState(finalStateWithoutSuccessor);
		}
		return atLeastOneStateRemoved;
	}

	/**
	 * Remove all states from which only finitely many accepting states are reachable.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public final void removeNonLiveStates() throws AutomataOperationCanceledException {
		boolean stateRemovedInInteration;
		do {
			if (mDeadEnds == null) {
				mDeadEnds = computeDeadEnds();
			}
			stateRemovedInInteration = removeDeadEnds();
			resetReachabilityInformation();
			stateRemovedInInteration |= removeAcceptingStatesWithoutSuccessors();
		} while (stateRemovedInInteration);
	}

	private void resetReachabilityInformation() {
		for (final STATE state : mTraversedNwa.getStates()) {
			final Map<STATE, ReachFinal> down2reachProp = mMarkedUp2Down.get(state);
			for (final STATE down : down2reachProp.keySet()) {
				down2reachProp.put(down, ReachFinal.UNKNOWN);
			}
		}
	}

	public long getDeadEndRemovalTime() {
		return mDeadEndRemovalTime;
	}

	/**
	 * @return Removed up-down entries.
	 */
	public Iterable<UpDownEntry<STATE>> getRemovedUpDownEntry() {
		return RemovedUpDownEntryIterator::new;
	}

	private Set<DoubleDecker<STATE>> removedDoubleDeckersOldMethod() {
		final Set<DoubleDecker<STATE>> result = new HashSet<>();
		for (final Entry<STATE, Map<STATE, ReachFinal>> entry : mMarkedUp2Down.entrySet()) {
			final STATE upState = entry.getKey();
			for (final Entry<STATE, ReachFinal> entry2 : entry.getValue().entrySet()) {
				if (entry2.getValue() == ReachFinal.UNKNOWN) {
					final STATE downState = entry2.getKey();
					result.add(new DoubleDecker<>(downState, upState));
				}
			}
		}
		return result;
	}

	private Set<DoubleDecker<STATE>> removedDoubleDeckersViaIterator() {
		final Set<DoubleDecker<STATE>> result = new HashSet<>();
		for (final UpDownEntry<STATE> upDownEntry : getRemovedUpDownEntry()) {
			result.add(new DoubleDecker<>(upDownEntry.getDown(), upDownEntry.getUp()));
		}
		return result;
	}

	/**
	 * Double decker set.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class DoubleDeckerSet {
		private final Map<STATE, Set<STATE>> mUp2down = new HashMap<>();

		/**
		 * @param upState
		 *            Up state.
		 * @param downState
		 *            down state
		 */
		public void add(final STATE upState, final STATE downState) {
			Set<STATE> downStates = mUp2down.get(upState);
			if (downStates == null) {
				downStates = new HashSet<>();
				mUp2down.put(upState, downStates);
			}
			downStates.add(downState);
		}

		/**
		 * @param collection
		 *            Collection of {@link DoubleDecker}s to add.
		 */
		public void addAll(final Collection<DoubleDecker<STATE>> collection) {
			for (final DoubleDecker<STATE> doubleDecker : collection) {
				this.add(doubleDecker.getUp(), doubleDecker.getDown());
			}
		}

		public Map<STATE, Set<STATE>> getUp2DownMap() {
			return mUp2down;
		}
	}

	/**
	 * Double decker work list.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class DoubleDeckerWorkList {
		private final Map<STATE, Set<STATE>> mUp2down;

		public DoubleDeckerWorkList() {
			mUp2down = new HashMap<>();
		}

		/**
		 * @param upState
		 *            Up state.
		 * @param downState
		 *            down state
		 */
		public void add(final STATE upState, final STATE downState) {
			Set<STATE> downStates = mUp2down.get(upState);
			if (downStates == null) {
				downStates = new HashSet<>();
				mUp2down.put(upState, downStates);
			}
			downStates.add(downState);
		}

		/**
		 * @param upState
		 *            Up state.
		 * @param moreDownStates
		 *            down states
		 */
		public void add(final STATE upState, final Collection<STATE> moreDownStates) {
			Set<STATE> downStates = mUp2down.get(upState);
			if (downStates == null) {
				downStates = new HashSet<>();
				mUp2down.put(upState, downStates);
			}
			downStates.addAll(moreDownStates);
		}

		public boolean isEmpty() {
			return mUp2down.isEmpty();
		}

		/**
		 * @return The next up state and its down states (removed from the map of this class).
		 */
		public Map<STATE, Set<STATE>> removeUpAndItsDowns() {
			final STATE up = mUp2down.keySet().iterator().next();
			final Map<STATE, Set<STATE>> result = Collections.singletonMap(up, mUp2down.remove(up));
			return result;
		}
	}

	/**
	 * Iterator for removed up-down entries.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private class RemovedUpDownEntryIterator implements Iterator<UpDownEntry<STATE>> {
		private final Iterator<STATE> mUpIterator;
		private STATE mUp;
		private Iterator<STATE> mDownIterator;
		private STATE mDown;
		private boolean mHasNext = true;

		public RemovedUpDownEntryIterator() {
			mUpIterator = getUp2DownMapping().keySet().iterator();
			if (mUpIterator.hasNext()) {
				mUp = mUpIterator.next();
				mDownIterator = getUp2DownMapping().get(mUp).keySet().iterator();
			} else {
				mHasNext = false;
			}
			computeNextElement();
		}

		private void computeNextElement() {
			mDown = null;
			while (mDown == null && mHasNext) {
				if (mDownIterator.hasNext()) {
					final STATE downCandidate = mDownIterator.next();
					final ReachFinal reach = getUp2DownMapping().get(mUp).get(downCandidate);
					if (reach == ReachFinal.UNKNOWN) {
						mDown = downCandidate;
					} else {
						assert reach == ReachFinal.AT_LEAST_ONCE;
					}
				} else {
					if (mUpIterator.hasNext()) {
						mUp = mUpIterator.next();
						mDownIterator = getUp2DownMapping().get(mUp).keySet().iterator();
					} else {
						mHasNext = false;
					}
				}
			}
		}

		@Override
		public boolean hasNext() {
			return mHasNext;
		}

		@Override
		@SuppressWarnings("squid:S1698")
		public UpDownEntry<STATE> next() {
			if (!hasNext()) {
				throw new NoSuchElementException();
			}
			STATE entry;
			final Set<STATE> callSuccs = computeState2CallSuccs(mDown);
			if (callSuccs.size() > 1) {
				throw new UnsupportedOperationException("State has more than one call successor");
			} else if (callSuccs.size() == 1) {
				entry = callSuccs.iterator().next();
			} else {
				entry = null;
				// equality intended here
				assert mDown == mTraversedNwa.getEmptyStackState();
			}
			final UpDownEntry<STATE> result = new UpDownEntry<>(mUp, mDown, entry);
			computeNextElement();
			return result;
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}

		/**
		 * Compute call successors for a given set of states.
		 */
		@SuppressWarnings("squid:S1698")
		private Set<STATE> computeState2CallSuccs(final STATE state) {
			final Set<STATE> callSuccs = new HashSet<>();
			// equality intended here
			if (state != mTraversedNwa.getEmptyStackState()) {
				for (final OutgoingCallTransition<LETTER, STATE> trans : mTraversedNwa.callSuccessors(state)) {
					callSuccs.add(trans.getSucc());
				}
			}
			return callSuccs;
		}
	}
}
