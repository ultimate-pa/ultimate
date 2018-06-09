/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DownStateConsistencyCheck;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval.UpDownEntry;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.AcceptingComponentsAnalysis.StronglyConnectedComponentWithAcceptanceInformation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.StateContainer.DownStateProp;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * A nested word automaton with reachable states information.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class NestedWordAutomatonReachableStates<LETTER, STATE>
		implements IDoubleDeckerAutomaton<LETTER, STATE>, IAutomatonWithSccComputation<LETTER, STATE> {

	public enum DoubleDeckerReachability { CAN_REACH_PRECIOUS, REACHABLE_AFTER_REMOVAL_OF_PRECIOUS_NOT_REACHERS }

	/**
	 * Construct a run for each accepting state. Use this only while developing/debugging/testing the construction of
	 * runs.
	 */
	private static final boolean EXT_RUN_CONSTRUCTION_TESTING = false;

	/**
	 * Construct a lasso for each accepting state/accepting summary. Use this only while developing/debugging/testing
	 * the construction of lassos.
	 */
	private static final boolean EXT_LASSO_CONSTRUCTION_TESTING = false;

	protected final IStateFactory<STATE> mStateFactory;

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;

	private final INwaOutgoingTransitionProvider<LETTER, STATE> mOperand;

	private final VpAlphabet<LETTER> mVpAlphabet;

	private final Set<STATE> mInitialStates = new HashSet<>();
	private final Set<STATE> mFinalStates = new HashSet<>();

	private final Map<STATE, StateContainer<LETTER, STATE>> mStates = new HashMap<>();

	/**
	 * Property of reachability.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	public enum ReachProp {
		REACHABLE,
		NODEADEND_AD,
		NODEADEND_SD,
		FINANC,
		LIVE_AD,
		LIVE_SD
	}

	/**
	 * Transition type.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	enum InCaRe {
		INTERNAL,
		CALL,
		RETURN,
		SUMMARY
	}

	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as map HierPREs -> LETTERs -> LinPREs ->
	 * SUCCs.
	 */
	private final Map<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> mReturnSummary = new HashMap<>();

	private final InCaReCounter mNumberTransitions = new InCaReCounter();

	/*
	 * private Map<StateContainer<LETTER, STATE>, Set<StateContainer<LETTER, STATE>>> mSummaries = new
	 * HashMap<StateContainer<LETTER, STATE>, Set<StateContainer<LETTER, STATE>>>();
	 */

	private final Set<LETTER> mEmptySetOfLetters = Collections.emptySet();

	private AncestorComputation mWithOutDeadEnds;
	private AncestorComputation mOnlyLiveStates;
	private AcceptingSummariesComputation mAcceptingSummaries;
	private AcceptingComponentsAnalysis<LETTER, STATE> mAcceptingComponentsAnalysis;

	/*
	 * private void addSummary(StateContainer<LETTER, STATE> callPred, StateContainer<LETTER, STATE> returnSucc) {
	 * Set<StateContainer<LETTER, STATE>> returnSuccs = mSummaries.get(callPred); if (returnSuccs == null) { returnSuccs
	 * = new HashSet<StateContainer<LETTER, STATE>>(); mSummaries.put(callPred, returnSuccs); }
	 * returnSuccs.add(returnSucc); }
	 */

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	public NestedWordAutomatonReachableStates(final AutomataLibraryServices services,
			final INwaOutgoingTransitionProvider<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mOperand = operand;
		mVpAlphabet = operand.getVpAlphabet();
		mStateFactory = operand.getStateFactory();
		try {
			new ReachableStatesComputation();
			// computeDeadEnds();
			// new NonLiveStateComputation();
			if (EXT_LASSO_CONSTRUCTION_TESTING) {
				final List<NestedLassoRun<LETTER, STATE>> runs =
						getOrComputeAcceptingComponents().getAllNestedLassoRuns();
				for (final NestedLassoRun<LETTER, STATE> nlr : runs) {
					final STATE honda = nlr.getLoop().getStateAtPosition(0);
					mLogger.debug(new DebugMessage("Test lasso construction for honda state {0}", honda));
					assertBuchiAcceptance(nlr);
				}
			}
			// assert (new TransitionConsitenceCheck<LETTER,
			// STATE>(this)).consistentForAll();

			assert checkTransitionsReturnedConsistent();
		} catch (final ToolchainCanceledException tce) {
			throw tce;
		} catch (final Error | RuntimeException e) {
			// final String message = "// Problem with RemoveUnreachable";
			// ResultChecker.writeToFileIfPreferred(mServices, "FailedremoveUnreachable", message, operand);
			throw e;
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(stateContainerInformation());
		}
		assert new DownStateConsistencyCheck<>(mServices, this).getResult() : "down states inconsistent";
	}

	private AutomataLibraryServices getServices() {
		return mServices;
	}

	private Map<STATE, StateContainer<LETTER, STATE>> getStatesMap() {
		return mStates;
	}

	private Collection<STATE> getInitialStatesPrivate() {
		return mInitialStates;
	}

	private Collection<STATE> getFinalStatesPrivate() {
		return mFinalStates;
	}

	private InCaReCounter getNumberTransitions() {
		return mNumberTransitions;
	}

	private void assertBuchiAcceptance(final NestedLassoRun<LETTER, STATE> nlr) throws AssertionError {
		try {
			assert new BuchiAccepts<>(mServices, NestedWordAutomatonReachableStates.this, nlr.getNestedLassoWord())
					.getResult();
		} catch (final AutomataLibraryException e) {
			throw new AssertionError(e);
		}
	}

	/**
	 * Returns the state container for a given state. The visibility of this method is deliberately set package private.
	 */
	StateContainer<LETTER, STATE> getStateContainer(final STATE state) {
		return mStates.get(state);
	}

	private String stateContainerInformation() {
		int inMap = 0;
		int outMap = 0;
		for (final Entry<STATE, StateContainer<LETTER, STATE>> entry : mStates.entrySet()) {
			final StateContainer<LETTER, STATE> cont = entry.getValue();
			if (cont instanceof StateContainerFieldAndMap) {
				if (((StateContainerFieldAndMap<LETTER, STATE>) cont).mapModeIncoming()) {
					inMap++;
				}
				if (((StateContainerFieldAndMap<LETTER, STATE>) cont).mapModeOutgoing()) {
					outMap++;
				}
			}
		}
		return mStates.size() + " StateContainers " + inMap + " in inMapMode" + outMap + " in outMapMode";
	}

	/*
	 * public boolean isDeadEnd(STATE state) { ReachProp reachProp = mStates.get(state).getReachProp(); return reachProp
	 * == ReachProp.REACHABLE; }
	 */

	public AncestorComputation getWithOutDeadEnds() {
		return mWithOutDeadEnds;
	}

	public AncestorComputation getOnlyLiveStates() {
		return mOnlyLiveStates;
	}

	/**
	 * @return The accepting components.
	 */
	public final AcceptingComponentsAnalysis<LETTER, STATE> getOrComputeAcceptingComponents() {
		if (mAcceptingComponentsAnalysis == null) {
			computeAcceptingComponents();
		}
		return mAcceptingComponentsAnalysis;
	}

	public AcceptingSummariesComputation getAcceptingSummariesComputation() {
		return mAcceptingSummaries;
	}

	/**
	 * @param state
	 *            A state.
	 * @return the respective state container
	 */
	StateContainer<LETTER, STATE> obtainStateContainer(final STATE state) {
		return mStates.get(state);
	}

	boolean isAccepting(final Summary<LETTER, STATE> summary) {
		final StateContainer<LETTER, STATE> callPred = summary.getHierPred();
		final Set<Summary<LETTER, STATE>> summariesForHier =
				mAcceptingSummaries.getAcceptingSummaries().getImage(callPred);
		if (summariesForHier == null) {
			return false;
		}
		return summariesForHier.contains(summary);
	}

	@Override
	public int size() {
		return mStates.size();
	}

	@Override
	public String sizeInformation() {
		final int states = mStates.size();
		String result = states + " states and " + mNumberTransitions + " transitions.";
		if (mAcceptingComponentsAnalysis != null) {
			final int transitions = mNumberTransitions.getSum();
			final int cyclomaticComplexity =
					computeCyclomaticComplexity(transitions, states, mAcceptingComponentsAnalysis.getSccComputation().getBalls().size());
			result += " cyclomatic complexity: " + cyclomaticComplexity;
		}
		return result;
	}

	private static int computeCyclomaticComplexity(final int numberOfTransitions, final int numberOfStates,
			final int numberOfSccs) {
		return numberOfTransitions - numberOfStates + numberOfSccs;
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mVpAlphabet;
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public Set<STATE> getStates() {
		return mStates.keySet();
	}

	@Override
	public Set<STATE> getInitialStates() {
		return Collections.unmodifiableSet(mInitialStates);
	}

	@Override
	public Collection<STATE> getFinalStates() {
		return Collections.unmodifiableSet(mFinalStates);
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mOperand.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return mOperand.isFinal(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return mOperand.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		return mStates.get(state).lettersInternal();
	}

	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		return mStates.get(state).lettersCall();
	}

	@Override
	public Set<LETTER> lettersReturn(final STATE state, final STATE hier) {
		return mStates.get(state).lettersReturn(hier);
	}

	@Override
	public Set<LETTER> lettersReturn(final STATE state) {
		return mStates.get(state).lettersReturn();
	}

	@Override
	public Set<LETTER> lettersInternalIncoming(final STATE state) {
		return mStates.get(state).lettersInternalIncoming();
	}

	@Override
	public Set<LETTER> lettersCallIncoming(final STATE state) {
		return mStates.get(state).lettersCallIncoming();
	}

	@Override
	public Set<LETTER> lettersReturnIncoming(final STATE state) {
		return mStates.get(state).lettersReturnIncoming();
	}

	@Override
	public Set<LETTER> lettersSummary(final STATE state) {
		if (!mStates.containsKey(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		return lettersSummaryNoAssertion(state);
	}

	private Iterable<STATE> succInternal(final STATE state, final LETTER letter) {
		return mStates.get(state).succInternal(letter);
	}

	private Iterable<STATE> succCall(final STATE state, final LETTER letter) {
		return mStates.get(state).succCall(letter);
	}

	@Override
	public Iterable<STATE> hierarchicalPredecessorsOutgoing(final STATE state, final LETTER letter) {
		return mStates.get(state).hierPred(letter);
	}

	private Iterable<STATE> succReturn(final STATE state, final STATE hier, final LETTER letter) {
		return mStates.get(state).succReturn(hier, letter);
	}

	private Iterable<STATE> predInternal(final STATE state, final LETTER letter) {
		return mStates.get(state).predInternal(letter);
	}

	private Iterable<STATE> predCall(final STATE state, final LETTER letter) {
		return mStates.get(state).predCall(letter);
	}

	void addReturnSummary(final STATE pred, final STATE hier, final LETTER letter, final STATE succ) {
		Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = mReturnSummary.get(hier);
		if (letter2pred2succs == null) {
			letter2pred2succs = new HashMap<>();
			mReturnSummary.put(hier, letter2pred2succs);
		}
		Map<STATE, Set<STATE>> pred2succs = letter2pred2succs.get(letter);
		if (pred2succs == null) {
			pred2succs = new HashMap<>();
			letter2pred2succs.put(letter, pred2succs);
		}
		Set<STATE> succS = pred2succs.get(pred);
		if (succS == null) {
			succS = new HashSet<>();
			pred2succs.put(pred, succS);
		}
		succS.add(succ);
	}

	/**
	 * @param hier
	 *            The hierarchical predecessor state.
	 * @return summary letters with the given hierarchical predecessor state
	 */
	public Set<LETTER> lettersSummaryNoAssertion(final STATE hier) {
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnSummary.get(hier);
		return map == null ? mEmptySetOfLetters : map.keySet();
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier, final LETTER letter) {
		final Set<SummaryReturnTransition<LETTER, STATE>> result = new HashSet<>();
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succ = mReturnSummary.get(hier);
		if (letter2pred2succ == null) {
			return result;
		}
		final Map<STATE, Set<STATE>> pred2succ = letter2pred2succ.get(letter);
		if (pred2succ == null) {
			return result;
		}
		for (final Entry<STATE, Set<STATE>> entry : pred2succ.entrySet()) {
			final STATE pred = entry.getKey();
			final Set<STATE> succs = entry.getValue();
			if (succs != null) {
				for (final STATE succ : succs) {
					final SummaryReturnTransition<LETTER, STATE> srt =
							new SummaryReturnTransition<>(pred, letter, succ);
					result.add(srt);
				}
			}
		}
		return result;
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier) {
		return () -> new Iterator<SummaryReturnTransition<LETTER, STATE>>() {
			private Iterator<LETTER> mLetterIterator;
			private LETTER mCurrentLetter;
			private Iterator<SummaryReturnTransition<LETTER, STATE>> mCurrentIterator;

			{
				mLetterIterator = lettersSummaryNoAssertion(hier).iterator();
				nextLetter();
			}

			private void nextLetter() {
				if (mLetterIterator.hasNext()) {
					do {
						mCurrentLetter = mLetterIterator.next();
						mCurrentIterator = summarySuccessors(hier, mCurrentLetter).iterator();
					} while (!mCurrentIterator.hasNext() && mLetterIterator.hasNext());
					if (!mCurrentIterator.hasNext()) {
						mCurrentLetter = null;
						mCurrentIterator = null;
					}
				} else {
					mCurrentLetter = null;
					mCurrentIterator = null;
				}
			}

			@Override
			public boolean hasNext() {
				return mCurrentLetter != null;
			}

			@Override
			public SummaryReturnTransition<LETTER, STATE> next() {
				if (mCurrentLetter == null) {
					throw new NoSuchElementException();
				}
				final SummaryReturnTransition<LETTER, STATE> result = mCurrentIterator.next();
				if (!mCurrentIterator.hasNext()) {
					nextLetter();
				}
				return result;
			}
		};
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ,
			final LETTER letter) {
		return mStates.get(succ).internalPredecessors(letter);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ) {
		return mStates.get(succ).internalPredecessors();
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ, final LETTER letter) {
		return mStates.get(succ).callPredecessors(letter);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ) {
		return mStates.get(succ).callPredecessors();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		return mStates.get(state).internalSuccessors(letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		return mStates.get(state).internalSuccessors();
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		return mStates.get(state).callSuccessors(letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		return mStates.get(state).callSuccessors();
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final STATE hier,
			final LETTER letter) {
		return mStates.get(succ).returnPredecessors(hier, letter);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final LETTER letter) {
		return mStates.get(succ).returnPredecessors(letter);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ) {
		return mStates.get(succ).returnPredecessors();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		return mStates.get(state).returnSuccessors(hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state) {
		return mStates.get(state).returnSuccessors();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		return mStates.get(state).returnSuccessorsGivenHier(hier);
	}

	/**
	 * Computes the dead ends.
	 */
	public void computeDeadEnds() {
		if (mWithOutDeadEnds != null) {
			return;
			// throw new AssertionError("dead are already computed");
		}
		final HashSet<StateContainer<LETTER, STATE>> acceptings = new HashSet<>();
		for (final STATE fin : getFinalStates()) {
			final StateContainer<LETTER, STATE> cont = mStates.get(fin);
			assert cont.getReachProp() != ReachProp.NODEADEND_AD && cont.getReachProp() != ReachProp.NODEADEND_SD;
			acceptings.add(cont);
		}
		mWithOutDeadEnds = new AncestorComputation(acceptings, ReachProp.NODEADEND_AD, ReachProp.NODEADEND_SD,
				DownStateProp.REACH_FINAL_ONCE, DownStateProp.REACHABLE_AFTER_DEADEND_REMOVAL);
	}

	/**
	 * Computes the accepting components.
	 */
	public void computeAcceptingComponents() {
		if (mAcceptingComponentsAnalysis != null) {
			throw new AssertionError("SCCs are already computed");
		}
		assert mAcceptingSummaries == null;
		mAcceptingSummaries = new AcceptingSummariesComputation();
		mAcceptingComponentsAnalysis = new AcceptingComponentsAnalysis<>(mServices, this, mAcceptingSummaries,
				mStates.keySet(), mInitialStates);
	}

	/**
	 * Computes the non-live states.
	 */
	public void computeNonLiveStates() {
		if (mOnlyLiveStates != null) {
			return;
			// throw new AssertionError("non-live states are already computed");
		}
		if (getOrComputeAcceptingComponents() == null) {
			computeAcceptingComponents();
		}

		final HashSet<StateContainer<LETTER, STATE>> nonLiveStartingSet =
				new HashSet<>(mAcceptingComponentsAnalysis.getStatesOfAllSccs());
		mOnlyLiveStates = new AncestorComputation(nonLiveStartingSet, ReachProp.LIVE_AD, ReachProp.LIVE_SD,
				DownStateProp.REACH_FINAL_INFTY, DownStateProp.REACHABLE_AFTER_NONLIVE_REMOVAL);
	}

	@Override
	public Set<STATE> getDownStates(final STATE upState) {
		final StateContainer<LETTER, STATE> cont = mStates.get(upState);
		return cont.getDownStates().keySet();
	}

	@Override
	public boolean isDoubleDecker(final STATE upState, final STATE downState) {
		return getDownStates(upState).contains(downState);
	}

	// //////////////////////////////////////////////////////////////////////////
	// Auxiliary Methods

	/**
	 * @param collection
	 *            A collection.
	 * @param <E>
	 *            collection elements type
	 * @return {@code true} iff the collection does not contain any {@code null} element
	 */
	public static <E> boolean noElementIsNull(final Collection<E> collection) {
		for (final E elem : collection) {
			if (elem == null) {
				return false;
			}
		}
		return true;
	}

	@Override
	public String toString() {
		return new AutomatonDefinitionPrinter<String, String>(mServices, "nwa", Format.ATS, this)
				.getDefinitionAsString();
	}

	@Override
	public Collection<StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE>>
			computeBalls(final Set<STATE> stateSubset, final Set<STATE> startStates) {
		if (!getStates().containsAll(stateSubset)) {
			throw new IllegalArgumentException("not a subset of the automaton's states: " + stateSubset);
		}
		if (!stateSubset.containsAll(startStates)) {
			throw new IllegalArgumentException("start states must be restricted to your subset");
		}

		if (mAcceptingSummaries == null) {
			mAcceptingSummaries = new AcceptingSummariesComputation();
		}
		final AcceptingComponentsAnalysis<LETTER, STATE> sccComputation =
				new AcceptingComponentsAnalysis<>(mServices, this, mAcceptingSummaries, stateSubset, startStates);
		return sccComputation.getSccComputation().getBalls();
	}

	// //////////////////////////////////////////////////////////////////////////
	// Methods to check correctness

	/**
	 * @param state
	 *            The predecessor state.
	 * @param letter
	 *            letter
	 * @param succ
	 *            successor state
	 * @return {@code true} iff the automaton contains the respective internal transition
	 */
	public boolean containsInternalTransition(final STATE state, final LETTER letter, final STATE succ) {
		return mStates.get(state).containsInternalTransition(letter, succ);
	}

	/**
	 * @param state
	 *            The predecessor state.
	 * @param letter
	 *            letter
	 * @param succ
	 *            successor state
	 * @return {@code true} iff the automaton contains the respective call transition
	 */
	public boolean containsCallTransition(final STATE state, final LETTER letter, final STATE succ) {
		return mStates.get(state).containsCallTransition(letter, succ);
	}

	/**
	 * @param lin
	 *            The linear predecessor state.
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            letter
	 * @param succ
	 *            successor state
	 * @return {@code true} iff the automaton contains the respective return transition
	 */
	public boolean containsReturnTransition(final STATE lin, final STATE hier, final LETTER letter, final STATE succ) {
		return mStates.get(lin).containsReturnTransition(hier, letter, succ);
	}

	/**
	 * @param lin
	 *            The linear predecessor state.
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            letter
	 * @param succ
	 *            successor state
	 * @return {@code true} iff the automaton contains the respective summary transition
	 */
	protected boolean containsSummaryReturnTransition(final STATE lin, final STATE hier, final LETTER letter,
			final STATE succ) {
		for (final SummaryReturnTransition<LETTER, STATE> trans : summarySuccessors(hier, letter)) {
			if (succ.equals(trans.getSucc()) && lin.equals(trans.getLinPred())) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @return {@code true} iff all transitions are consistent.
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	final boolean checkTransitionsReturnedConsistent() throws AutomataOperationCanceledException {
		boolean result = true;
		for (final STATE state : getStates()) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}

			for (final IncomingInternalTransition<LETTER, STATE> inTrans : internalPredecessors(state)) {
				result &= containsInternalTransition(inTrans.getPred(), inTrans.getLetter(), state);
				assert result;
				final StateContainer<LETTER, STATE> cont = mStates.get(state);
				result &= cont.lettersInternalIncoming().contains(inTrans.getLetter());
				assert result;
				result &= cont.predInternal(inTrans.getLetter()).contains(inTrans.getPred());
				assert result;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans : internalSuccessors(state)) {
				result &= containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert result;
				final StateContainer<LETTER, STATE> cont = mStates.get(state);
				result &= cont.lettersInternal().contains(outTrans.getLetter());
				assert result;
				result &= cont.succInternal(outTrans.getLetter()).contains(outTrans.getSucc());
				assert result;
			}
			for (final IncomingCallTransition<LETTER, STATE> inTrans : callPredecessors(state)) {
				result &= containsCallTransition(inTrans.getPred(), inTrans.getLetter(), state);
				assert result;
				final StateContainer<LETTER, STATE> cont = mStates.get(state);
				result &= cont.lettersCallIncoming().contains(inTrans.getLetter());
				assert result;
				result &= cont.predCall(inTrans.getLetter()).contains(inTrans.getPred());
				assert result;
			}
			for (final OutgoingCallTransition<LETTER, STATE> outTrans : callSuccessors(state)) {
				result &= containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert result;
				final StateContainer<LETTER, STATE> cont = mStates.get(state);
				result &= cont.lettersCall().contains(outTrans.getLetter());
				assert result;
				result &= cont.succCall(outTrans.getLetter()).contains(outTrans.getSucc());
				assert result;
			}
			for (final IncomingReturnTransition<LETTER, STATE> inTrans : returnPredecessors(state)) {
				result &= containsReturnTransition(inTrans.getLinPred(), inTrans.getHierPred(), inTrans.getLetter(),
						state);
				assert result;
				result &= containsSummaryReturnTransition(inTrans.getLinPred(), inTrans.getHierPred(),
						inTrans.getLetter(), state);
				assert result;
				final StateContainer<LETTER, STATE> cont = mStates.get(state);
				result &= cont.lettersReturnIncoming().contains(inTrans.getLetter());
				assert result;
				result &= cont.predReturnHier(inTrans.getLetter()).contains(inTrans.getHierPred());
				assert result;
				result &= cont.predReturnLin(inTrans.getLetter(), inTrans.getHierPred()).contains(inTrans.getLinPred());
				assert result;
			}
			for (final OutgoingReturnTransition<LETTER, STATE> outTrans : returnSuccessors(state)) {
				result &= containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(),
						outTrans.getSucc());
				assert result;
				result &= containsSummaryReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(),
						outTrans.getSucc());
				assert result;
				final StateContainer<LETTER, STATE> cont = mStates.get(state);
				result &= cont.lettersReturn().contains(outTrans.getLetter());
				assert result;
				result &= cont.hierPred(outTrans.getLetter()).contains(outTrans.getHierPred());
				assert result;
				result &= cont.succReturn(outTrans.getHierPred(), outTrans.getLetter()).contains(outTrans.getSucc());
				assert result;
			}

			/*
			 * for (LETTER letter : lettersReturnSummary(state)) { for (SummaryReturnTransition<LETTER, STATE> sumTrans
			 * : returnSummarySuccessor(letter, state)) { result &= containsReturnTransition(state,
			 * sumTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc()); assert result; StateContainer<LETTER,
			 * STATE> cont = mStates.get(state); result &= cont.lettersReturn().contains(outTrans.getLetter()); assert
			 * result; result &= cont.hierPred(outTrans.getLetter()).contains(outTrans.getHierPred()); assert result;
			 * result &= cont.succReturn(outTrans.getHierPred(), outTrans.getLetter()).contains(outTrans.getSucc());
			 * assert result; } }
			 */

			for (final OutgoingInternalTransition<LETTER, STATE> trans : internalSuccessors(state)) {
				result &= containsInternalTransition(state, trans.getLetter(), trans.getSucc());
				assert result;
			}
			for (final OutgoingCallTransition<LETTER, STATE> trans : callSuccessors(state)) {
				result &= containsCallTransition(state, trans.getLetter(), trans.getSucc());
				assert result;
			}
			for (final OutgoingReturnTransition<LETTER, STATE> trans : returnSuccessors(state)) {
				result &= containsReturnTransition(state, trans.getHierPred(), trans.getLetter(), trans.getSucc());
				assert result;
			}
			for (final IncomingInternalTransition<LETTER, STATE> trans : internalPredecessors(state)) {
				result &= containsInternalTransition(trans.getPred(), trans.getLetter(), state);
				assert result;
			}
			for (final IncomingCallTransition<LETTER, STATE> trans : callPredecessors(state)) {
				result &= containsCallTransition(trans.getPred(), trans.getLetter(), state);
				assert result;
			}
			for (final IncomingReturnTransition<LETTER, STATE> inTrans : returnPredecessors(state)) {
				result &= containsReturnTransition(inTrans.getLinPred(), inTrans.getHierPred(), inTrans.getLetter(),
						state);
				assert result;
			}
		}

		return result;
	}

	@SuppressWarnings("squid:S1698")
	boolean checkStateEquality(final STATE state1, final STATE state2) {
		return state1 == state2;
	}

	@SuppressWarnings("squid:S1698")
	boolean checkStateContainerEquality(final StateContainer<LETTER, STATE> cont,
			final StateContainer<LETTER, STATE> succCont) {
		return cont == succCont;
	}

	// //////////////////////////////////////////////////////////////////////////

	/**
	 * Compute the set of reachable double deckers. Construct a state container for each reachable state, add both
	 * (state and StateContainer) to mStates and set the reachability down state information in the state container.
	 */
	private class ReachableStatesComputation {
		private static final String OPERAND_CONTAINS_TRANSITION_TWICE = "Operand contains transition twice: ";
		private int mNumberOfConstructedStates;
		private final LinkedList<StateContainer<LETTER, STATE>> mForwardWorklist = new LinkedList<>();
		private final LinkedList<StateContainer<LETTER, STATE>> mDownPropagationWorklist = new LinkedList<>();

		ReachableStatesComputation() throws AutomataOperationCanceledException {
			addInitialStates(mOperand.getInitialStates());

			do {
				while (!mForwardWorklist.isEmpty()) {
					if (!getServices().getProgressAwareTimer().continueProcessing()) {
						final RunningTaskInfo rti = constructRunningTaskInfo();
						throw new AutomataOperationCanceledException(rti);
					}
					final StateContainer<LETTER, STATE> cont = mForwardWorklist.remove(0);
					cont.eraseUnpropagatedDownStates();
					Set<STATE> newDownStatesFormSelfloops = null;

					if (candidateForOutgoingReturn(cont.getState())) {
						for (final STATE down : cont.getDownStates().keySet()) {
							if (!checkStateEquality(down, getEmptyStackState())) {
								final Set<STATE> newDownStates = addReturnsAndSuccessors(cont, down);
								if (newDownStates != null) {
									if (newDownStatesFormSelfloops == null) {
										newDownStatesFormSelfloops = new HashSet<>();
									}
									newDownStatesFormSelfloops.addAll(newDownStates);
								}
							}
						}
					}
					addInternalsAndSuccessors(cont);
					final Set<STATE> newDownStates = addCallsAndSuccessors(cont);
					if (newDownStates != null) {
						if (newDownStatesFormSelfloops == null) {
							newDownStatesFormSelfloops = new HashSet<>();
						}
						newDownStatesFormSelfloops.addAll(newDownStates);
					}
					if (newDownStatesFormSelfloops != null) {
						assert !newDownStatesFormSelfloops.isEmpty();
						for (final STATE down : newDownStatesFormSelfloops) {
							cont.addReachableDownState(down);
						}
						mDownPropagationWorklist.add(cont);
					}
				}
				while (mForwardWorklist.isEmpty() && !mDownPropagationWorklist.isEmpty()) {
					if (!getServices().getProgressAwareTimer().continueProcessing()) {
						// TODO: Check if this has a performance impact
						// This exception was included because of timeouts on
						// e.g.
						// svcomp/systemc/token_ring.07_false-unreach-call_false-termination.cil.c
						// (Settings:settings/TACASInterpolation2015/ForwardPredicates.epf,
						// Toolchain:toolchains/AutomizerC.xml)
						final RunningTaskInfo rti = constructRunningTaskInfo();
						throw new AutomataOperationCanceledException(rti);
					}

					final StateContainer<LETTER, STATE> cont = mDownPropagationWorklist.remove(0);
					propagateNewDownStates(cont);
				}

			} while (!mDownPropagationWorklist.isEmpty() || !mForwardWorklist.isEmpty());
			assert mForwardWorklist.isEmpty();
			assert mDownPropagationWorklist.isEmpty();
			assert checkTransitionsReturnedConsistent();

			if (EXT_RUN_CONSTRUCTION_TESTING) {
				for (final STATE fin : getFinalStates()) {
					mLogger.debug(new DebugMessage("Test if can find an accepting run for final state {0}", fin));
					final NestedRun<LETTER, STATE> run = new RunConstructor<>(getServices(),
							NestedWordAutomatonReachableStates.this, mStates.get(fin)).constructRun();
					try {
						assert new Accepts<>(getServices(), NestedWordAutomatonReachableStates.this, run.getWord())
								.getResult();
					} catch (final AutomataLibraryException e) {
						throw new AssertionError(e);
					}
				}
			}
		}

		private RunningTaskInfo constructRunningTaskInfo() {
			final String taskDescription = "computing reachable states (" + mNumberOfConstructedStates
					+ " states constructed" + "input type " + mOperand.getClass().getSimpleName() + ")";
			final RunningTaskInfo rti = new RunningTaskInfo(getClass(), taskDescription);
			return rti;
		}

		private void addInitialStates(final Iterable<STATE> initialStates) {
			for (final STATE state : initialStates) {
				getInitialStatesPrivate().add(state);
				final HashMap<STATE, Integer> downStates = new HashMap<>();
				downStates.put(getEmptyStackState(), Integer.valueOf(0));
				final StateContainer<LETTER, STATE> sc = addState(state, downStates);
				getStatesMap().put(state, sc);
			}
		}

		/**
		 * Construct State Container. Add to CommonEntriesComponent. Add to ForwardWorklist.
		 */
		private StateContainer<LETTER, STATE> addState(final STATE state, final HashMap<STATE, Integer> downStates) {
			assert !getStatesMap().containsKey(state);
			if (mOperand.isFinal(state)) {
				getFinalStatesPrivate().add(state);
			}
			final boolean canHaveOutgoingReturn = candidateForOutgoingReturn(state);
			final StateContainer<LETTER, STATE> result = new StateContainerFieldAndMap<>(state,
					mNumberOfConstructedStates, downStates, canHaveOutgoingReturn);
			mNumberOfConstructedStates++;
			getStatesMap().put(state, result);
			mForwardWorklist.add(result);
			return result;
		}

		private boolean candidateForOutgoingReturn(final STATE state) {
			if (mOperand.hasModifiableAlphabet()) {
				return true;
			}
			if (getVpAlphabet().getReturnAlphabet().isEmpty()) {
				return false;
			}
			return true;
		}

		private void addInternalsAndSuccessors(final StateContainer<LETTER, STATE> cont) throws AutomataOperationCanceledException {
			final STATE state = cont.getState();
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(state)) {
				if (!getServices().getProgressAwareTimer().continueProcessing()) {
					final RunningTaskInfo rti = constructRunningTaskInfo();
					throw new AutomataOperationCanceledException(rti);
				}
				final STATE succ = trans.getSucc();
				StateContainer<LETTER, STATE> succSc = getStatesMap().get(succ);
				if (succSc == null) {
					succSc = addState(succ, new HashMap<>(cont.getDownStates()));
				} else {
					addNewDownStates(cont, succSc, cont.getDownStates().keySet());
				}
				assert !containsCallTransition(state, trans.getLetter(), succ) : OPERAND_CONTAINS_TRANSITION_TWICE
						+ state + trans.getSucc();
				cont.addInternalOutgoing(trans);
				succSc.addInternalIncoming(new IncomingInternalTransition<>(state, trans.getLetter()));
				getNumberTransitions().incIn();
			}
		}

		private Set<STATE> addCallsAndSuccessors(final StateContainer<LETTER, STATE> cont) throws AutomataOperationCanceledException {
			boolean addedSelfloop = false;
			final STATE state = cont.getState();
			for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(cont.getState())) {
				if (!getServices().getProgressAwareTimer().continueProcessing()) {
					final RunningTaskInfo rti = constructRunningTaskInfo();
					throw new AutomataOperationCanceledException(rti);
				}
				final STATE succ = trans.getSucc();
				StateContainer<LETTER, STATE> succCont = getStatesMap().get(succ);
				final HashMap<STATE, Integer> succDownStates = new HashMap<>();
				succDownStates.put(cont.getState(), Integer.valueOf(0));
				if (succCont == null) {
					succCont = addState(succ, succDownStates);
				} else {
					addNewDownStates(cont, succCont, succDownStates.keySet());
					if (checkStateContainerEquality(cont, succCont)) {
						addedSelfloop = true;
					}
				}
				assert !containsCallTransition(state, trans.getLetter(), succ) : OPERAND_CONTAINS_TRANSITION_TWICE
						+ state + trans.getSucc();
				cont.addCallOutgoing(trans);
				succCont.addCallIncoming(new IncomingCallTransition<>(state, trans.getLetter()));
				getNumberTransitions().incCa();
			}
			if (addedSelfloop) {
				final HashSet<STATE> newDownStates = new HashSet<>(1);
				newDownStates.add(state);
				return newDownStatesSelfloop(cont, newDownStates);
			}
			return null;
		}

		private Set<STATE> addReturnsAndSuccessors(final StateContainer<LETTER, STATE> cont, final STATE down) throws AutomataOperationCanceledException {
			boolean addedSelfloop = false;
			final STATE state = cont.getState();
			StateContainer<LETTER, STATE> downCont = null;
			for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessorsGivenHier(state,
					down)) {
				if (!getServices().getProgressAwareTimer().continueProcessing()) {
					final RunningTaskInfo rti = constructRunningTaskInfo();
					throw new AutomataOperationCanceledException(rti);
				}
				assert down.equals(trans.getHierPred());
				if (downCont == null) {
					downCont = getStatesMap().get(down);
				}
				final STATE succ = trans.getSucc();
				StateContainer<LETTER, STATE> succCont = getStatesMap().get(succ);
				if (succCont == null) {
					succCont = addState(succ, new HashMap<>(downCont.getDownStates()));
				} else {
					addNewDownStates(cont, succCont, downCont.getDownStates().keySet());
					if (checkStateContainerEquality(cont, succCont)) {
						addedSelfloop = true;
					}
				}
				assert !containsReturnTransition(state, down, trans.getLetter(),
						succ) : OPERAND_CONTAINS_TRANSITION_TWICE + state + trans.getSucc();
				cont.addReturnOutgoing(trans);
				succCont.addReturnIncoming(new IncomingReturnTransition<>(cont.getState(), down, trans.getLetter()));
				addReturnSummary(state, down, trans.getLetter(), succ);
				getNumberTransitions().incRe();
				// addSummary(downCont, succCont);
			}
			if (addedSelfloop) {
				return newDownStatesSelfloop(cont, downCont.getDownStates().keySet());
			}
			return null;
		}

		private Set<STATE> newDownStatesSelfloop(final StateContainer<LETTER, STATE> cont,
				final Set<STATE> propagatedDownStates) {
			Set<STATE> newDownStates = null;
			for (final STATE downs : propagatedDownStates) {
				if (!cont.getDownStates().keySet().contains(downs)) {
					if (newDownStates == null) {
						newDownStates = new HashSet<>();
					}
					newDownStates.add(downs);
				}
			}
			return newDownStates;
		}

		private void addNewDownStates(final StateContainer<LETTER, STATE> cont,
				final StateContainer<LETTER, STATE> succCont, final Set<STATE> potentiallyNewDownStates) {
			if (checkStateContainerEquality(cont, succCont)) {
				return;
			}
			boolean newDownStateWasPropagated = false;
			for (final STATE down : potentiallyNewDownStates) {
				final boolean newlyAdded = succCont.addReachableDownState(down);
				if (newlyAdded) {
					newDownStateWasPropagated = true;
				}
			}
			if (newDownStateWasPropagated) {
				mDownPropagationWorklist.add(succCont);
			}
		}

		private void propagateNewDownStates(final StateContainer<LETTER, STATE> cont) throws AutomataOperationCanceledException {
			final Set<STATE> unpropagatedDownStates = cont.getUnpropagatedDownStates();
			if (unpropagatedDownStates == null) {
				return;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> trans : cont.internalSuccessors()) {
				final StateContainer<LETTER, STATE> succCont = getStatesMap().get(trans.getSucc());
				addNewDownStates(cont, succCont, unpropagatedDownStates);
			}
			for (final SummaryReturnTransition<LETTER, STATE> trans : summarySuccessors(cont.getState())) {
				final StateContainer<LETTER, STATE> succCont = getStatesMap().get(trans.getSucc());
				addNewDownStates(cont, succCont, unpropagatedDownStates);
			}
			if (candidateForOutgoingReturn(cont.getState())) {
				HashSet<STATE> newDownStatesFormSelfloops = null;
				for (final STATE down : cont.getUnpropagatedDownStates()) {
					if (!checkStateEquality(down, getEmptyStackState())) {
						final Set<STATE> newDownStates = addReturnsAndSuccessors(cont, down);
						if (newDownStates != null) {
							if (newDownStatesFormSelfloops == null) {
								newDownStatesFormSelfloops = new HashSet<>();
							}
							newDownStatesFormSelfloops.addAll(newDownStates);
						}
					}
				}
				cont.eraseUnpropagatedDownStates();
				if (newDownStatesFormSelfloops != null) {
					assert !newDownStatesFormSelfloops.isEmpty();
					for (final STATE down : newDownStatesFormSelfloops) {
						cont.addReachableDownState(down);
					}
					mDownPropagationWorklist.add(cont);
				}
			} else {
				cont.eraseUnpropagatedDownStates();
			}
		}
	}

	// //////////////////////////////////////////////////////////////////////////////
	/**
	 * Compute all ancestor double deckers for a given set of states which we call the precious states. (In a dead end
	 * computation the precious states are the final states, in a non-live computation the precious states are all
	 * states of accepting SCCs).
	 * <p>
	 * If a state <i>up</i> can reach a precious state via a run without pending returns, we known that all double
	 * deckers <i>(up,down)</i> can reach a precious state and <i>up</i> gets the property "allDownProp".
	 * <p>
	 * If a state <i>up</i> can reach a precious state only via a run with pending calls we identify the down states
	 * such that the double decker <i>(up,down)</i> can reach a precious state. The up state gets the property
	 * "someDownProp", and the double decker gets the property "downStateProp" (this information is stored in the state
	 * container of <i>up</i>.
	 */
	public class AncestorComputation {
		protected final ReachProp mRpAllDown;
		protected final ReachProp mRpSomeDown;

		/**
		 * Property stating that from this DoubleDecker precious states are reachable (resp reachable infinitely often).
		 */
		protected final DownStateProp mDspReachPrecious;
		/**
		 * Property stating that this DoubleDecker is reachable after removal of states.
		 */
		private final DownStateProp mDspReachableAfterRemoval;

		private final Set<STATE> mAncestors = new HashSet<>();
		private final Set<STATE> mAncestorsInitial = new HashSet<>();
		private final Set<STATE> mAncestorsAccepting = new HashSet<>();

		private final ArrayDeque<StateContainer<LETTER, STATE>> mNonReturnBackwardWorklist = new ArrayDeque<>();
		private final Set<StateContainer<LETTER, STATE>> mHasIncomingReturn = new HashSet<>();
		private final ArrayDeque<StateContainer<LETTER, STATE>> mPropagationWorklist = new ArrayDeque<>();

		AncestorComputation(final HashSet<StateContainer<LETTER, STATE>> preciousStates, final ReachProp allDownProp,
				final ReachProp someDownProp, final DownStateProp downStatePropReachPrecious,
				final DownStateProp downStatePropReachableAfterRemoval) {
			mRpAllDown = allDownProp;
			mRpSomeDown = someDownProp;
			mDspReachPrecious = downStatePropReachPrecious;
			mDspReachableAfterRemoval = downStatePropReachableAfterRemoval;

			for (final StateContainer<LETTER, STATE> cont : preciousStates) {
				cont.setReachProp(mRpAllDown);
				mAncestors.add(cont.getState());
				mNonReturnBackwardWorklist.add(cont);
			}

			while (!mNonReturnBackwardWorklist.isEmpty()) {
				final StateContainer<LETTER, STATE> cont = mNonReturnBackwardWorklist.removeFirst();
				if (getInitialStatesPrivate().contains(cont.getState())) {
					mAncestorsInitial.add(cont.getState());
				}
				if (isFinal(cont.getState())) {
					mAncestorsAccepting.add(cont.getState());
				}

				for (final IncomingInternalTransition<LETTER, STATE> inTrans : cont.internalPredecessors()) {
					final STATE pred = inTrans.getPred();
					final StateContainer<LETTER, STATE> predCont = getStatesMap().get(pred);
					if (predCont.getReachProp() != mRpAllDown) {
						predCont.setReachProp(mRpAllDown);
						mAncestors.add(pred);
						mNonReturnBackwardWorklist.add(predCont);
					}
				}
				for (final IncomingReturnTransition<LETTER, STATE> inTrans : cont.returnPredecessors()) {
					final STATE hier = inTrans.getHierPred();
					final StateContainer<LETTER, STATE> hierCont = getStatesMap().get(hier);
					if (hierCont.getReachProp() != mRpAllDown) {
						hierCont.setReachProp(mRpAllDown);
						mAncestors.add(hier);
						mNonReturnBackwardWorklist.add(hierCont);
					}
					mHasIncomingReturn.add(cont);
				}
				for (final IncomingCallTransition<LETTER, STATE> inTrans : cont.callPredecessors()) {
					final STATE pred = inTrans.getPred();
					final StateContainer<LETTER, STATE> predCont = getStatesMap().get(pred);
					if (predCont.getReachProp() != mRpAllDown) {
						predCont.setReachProp(mRpAllDown);
						mAncestors.add(pred);
						mNonReturnBackwardWorklist.add(predCont);
					}
				}
			}

			for (final StateContainer<LETTER, STATE> cont : mHasIncomingReturn) {
				for (final IncomingReturnTransition<LETTER, STATE> inTrans : cont.returnPredecessors()) {
					final STATE lin = inTrans.getLinPred();
					final StateContainer<LETTER, STATE> linCont = getStatesMap().get(lin);
					if (linCont.getReachProp() != mRpAllDown) {
						final Set<STATE> potentiallyNewDownStates = new HashSet<>(1);
						potentiallyNewDownStates.add(inTrans.getHierPred());
						addNewDownStates(null, linCont, potentiallyNewDownStates);
						/*
						 * if (linCont.getUnpropagatedDownStates() == null) { assert
						 * !mPropagationWorklist.contains(linCont); mPropagationWorklist.addLast(linCont); } ReachProp
						 * oldValue = linCont.modifyDownProp(inTrans.getHierPred(), mrpSomeDown); assert oldValue !=
						 * mrpAllDown;
						 */
					}
				}
			}

			while (!mPropagationWorklist.isEmpty()) {
				final StateContainer<LETTER, STATE> cont = mPropagationWorklist.removeFirst();
				propagateBackward(cont);
			}
			removeUnnecessaryInitialStates();
			propagateReachableAfterRemovalDoubleDeckers();
		}

		public Set<STATE> getStates() {
			return mAncestors;
		}

		public Set<STATE> getInitials() {
			return mAncestorsInitial;
		}

		public Set<STATE> getFinals() {
			return mAncestorsAccepting;
		}

		private void removeUnnecessaryInitialStates() {
			final Iterator<STATE> it = mAncestorsInitial.iterator();
			while (it.hasNext()) {
				final STATE state = it.next();
				final StateContainer<LETTER, STATE> cont = getStatesMap().get(state);
				if (cont.getReachProp() == mRpAllDown) {
					continue;
				}
				final boolean reachFinalOnce = cont.hasDownProp(getEmptyStackState(), DownStateProp.REACH_FINAL_ONCE);
				if (reachFinalOnce) {
					continue;
				}
				it.remove();
			}
		}

		private void propagateBackward(final StateContainer<LETTER, STATE> cont) {
			final Set<STATE> unpropagatedDownStates = cont.getUnpropagatedDownStates();
			cont.eraseUnpropagatedDownStates();
			Set<STATE> newUnpropagatedDownStatesSelfloop = null;
			for (final IncomingInternalTransition<LETTER, STATE> inTrans : cont.internalPredecessors()) {
				final STATE pred = inTrans.getPred();
				final StateContainer<LETTER, STATE> predCont = getStatesMap().get(pred);
				if (predCont.getReachProp() != mRpAllDown) {
					addNewDownStates(cont, predCont, unpropagatedDownStates);
				}
			}
			for (final IncomingReturnTransition<LETTER, STATE> inTrans : cont.returnPredecessors()) {
				final STATE hier = inTrans.getHierPred();
				final StateContainer<LETTER, STATE> hierCont = getStatesMap().get(hier);
				if (hierCont.getReachProp() != mRpAllDown) {
					addNewDownStates(cont, hierCont, unpropagatedDownStates);
				}
				final STATE lin = inTrans.getLinPred();
				final StateContainer<LETTER, STATE> linCont = getStatesMap().get(lin);
				if (linCont.getReachProp() != mRpAllDown
						&& atLeastOneOccursAsDownState(hierCont, unpropagatedDownStates)) {
					if (checkStateContainerEquality(linCont, cont)) {
						final boolean hierAlreadyPropagated = cont.hasDownProp(hier, mDspReachPrecious);
						if (!hierAlreadyPropagated) {
							if (newUnpropagatedDownStatesSelfloop == null) {
								newUnpropagatedDownStatesSelfloop = new HashSet<>();
							}
							newUnpropagatedDownStatesSelfloop.add(hier);
						}
					} else {
						final HashSet<STATE> potentiallyNewDownState = new HashSet<>(1);
						potentiallyNewDownState.add(hier);
						addNewDownStates(cont, linCont, potentiallyNewDownState);
					}
				}
			}
			if (newUnpropagatedDownStatesSelfloop != null) {
				for (final STATE down : newUnpropagatedDownStatesSelfloop) {
					cont.setDownProp(down, mDspReachPrecious);
				}
				assert !mPropagationWorklist.contains(cont);
				mPropagationWorklist.add(cont);
			}
		}

		private boolean atLeastOneOccursAsDownState(final StateContainer<LETTER, STATE> hierCont,
				final Set<STATE> unpropagatedDownStates) {
			for (final STATE state : unpropagatedDownStates) {
				if (hierCont.getDownStates().containsKey(state)) {
					return true;
				}
			}
			return false;
		}

		private void addNewDownStates(final StateContainer<LETTER, STATE> cont,
				final StateContainer<LETTER, STATE> predCont, final Set<STATE> potentiallyNewDownStates) {
			if (checkStateContainerEquality(cont, predCont)) {
				return;
			}
			final boolean isAlreadyInWorklist = predCont.getUnpropagatedDownStates() != null;
			assert isAlreadyInWorklist == mPropagationWorklist.contains(predCont);
			assert !isAlreadyInWorklist || predCont.getReachProp() == mRpSomeDown;
			boolean newDownStateWasPropagated = false;
			for (final STATE down : potentiallyNewDownStates) {
				if (predCont.getDownStates().containsKey(down)) {
					final boolean modified = predCont.setDownProp(down, mDspReachPrecious);
					if (modified) {
						newDownStateWasPropagated = true;
					}
				}
			}
			if (newDownStateWasPropagated) {
				if (!isAlreadyInWorklist) {
					assert !mPropagationWorklist.contains(predCont);
					mPropagationWorklist.add(predCont);
				}
				if (predCont.getReachProp() != mRpSomeDown) {
					assert predCont.getReachProp() != mRpAllDown;
					predCont.setReachProp(mRpSomeDown);
					assert !mAncestors.contains(predCont.getState());
					mAncestors.add(predCont.getState());
					if (isFinal(predCont.getState())) {
						mAncestorsAccepting.add(predCont.getState());
					}
				}
			}
		}

		/**
		 * Among all DoubleDeckers that cannot reach a precious state, there are some that are reachable (even after
		 * removing states that cannot reach precious states). This method marks all these DoubleDeckers with
		 * mDspReachableAfterRemoval
		 */
		public final void propagateReachableAfterRemovalDoubleDeckers() {
			final LinkedHashSet<StateContainer<LETTER, STATE>> propagationWorklist = new LinkedHashSet<>();
			final Set<StateContainer<LETTER, STATE>> visited = new HashSet<>();

			// start only at states that are still initial after removal of states
			for (final STATE state : mAncestorsInitial) {
				assert isInitial(state);
				final StateContainer<LETTER, STATE> sc = getStatesMap().get(state);
				propagationWorklist.add(sc);
				visited.add(sc);
			}

			while (!propagationWorklist.isEmpty()) {
				final StateContainer<LETTER, STATE> cont = propagationWorklist.iterator().next();
				propagationWorklist.remove(cont);
				for (final OutgoingInternalTransition<LETTER, STATE> inTrans : cont.internalSuccessors()) {
					final STATE succ = inTrans.getSucc();
					if (!mAncestors.contains(succ)) {
						// succ will be removed
						continue;
					}
					final StateContainer<LETTER, STATE> succCont = getStatesMap().get(succ);
					final boolean modified = propagateReachableAfterRemovalProperty(cont, succCont);
					addToWorklistIfModfiedOrNotVisited(propagationWorklist, visited, modified, succCont);
				}
				for (final SummaryReturnTransition<LETTER, STATE> inTrans : summarySuccessors(cont.getState())) {
					final STATE succ = inTrans.getSucc();
					if (!mAncestors.contains(succ)) {
						// succ will be removed
						continue;
					}
					final STATE lin = inTrans.getLinPred();
					if (!mAncestors.contains(lin)) {
						// linear predecessor will be removed
						continue;
					}
					{
						// if the (linPred, hierPred) DoubleDecker is not
						// reachable in the resulting automaton, then
						// this summary is not in the resulting automaton
						// hence we must not use it for propagation here
						final StateContainer<LETTER, STATE> linCont = getStatesMap().get(inTrans.getLinPred());
						final boolean summaryIsInResultAutomaton = checkDoubleDeckerProperty(linCont, cont.getState(),
								mRpAllDown, mRpSomeDown, mDspReachPrecious);
						if (!summaryIsInResultAutomaton) {
							continue;
						}
					}

					final StateContainer<LETTER, STATE> succCont = getStatesMap().get(succ);
					final boolean modified = propagateReachableAfterRemovalProperty(cont, succCont);
					addToWorklistIfModfiedOrNotVisited(propagationWorklist, visited, modified, succCont);
				}
				for (final OutgoingCallTransition<LETTER, STATE> inTrans : cont.callSuccessors()) {
					final STATE succ = inTrans.getSucc();
					if (!mAncestors.contains(succ)) {
						// succ will be removed
						continue;
					}

					final StateContainer<LETTER, STATE> succCont = getStatesMap().get(succ);
					final boolean modified = false;
					addToWorklistIfModfiedOrNotVisited(propagationWorklist, visited, modified, succCont);
				}
			}
		}

		private boolean checkDoubleDeckerProperty(final StateContainer<LETTER, STATE> up, final STATE down,
				final ReachProp rpAllDown, final ReachProp rpSomeDown, final DownStateProp dspReachPrecious)
				throws AssertionError {
			boolean result;
			if (up.getReachProp() == rpAllDown) {
				result = true;
			} else {
				if (up.getReachProp() == rpSomeDown) {
					assert up.getDownStates().containsKey(down);
					result = up.hasDownProp(down, dspReachPrecious);
				} else {
					throw new AssertionError("DoubleDecker cannot reach precious");
				}
			}
			return result;
		}

		private void addToWorklistIfModfiedOrNotVisited(
				final LinkedHashSet<StateContainer<LETTER, STATE>> propagationWorklist,
				final Set<StateContainer<LETTER, STATE>> visited, final boolean modified,
				final StateContainer<LETTER, STATE> succCont) {
			if (modified || !visited.contains(succCont)) {
				propagationWorklist.add(succCont);
				visited.add(succCont);
			}
		}

		/**
		 * Returns true if property was modified.
		 */
		private boolean propagateReachableAfterRemovalProperty(final StateContainer<LETTER, STATE> cont,
				final StateContainer<LETTER, STATE> succCont) throws AssertionError {
			boolean modified = false;
			if (succCont.getReachProp() == mRpAllDown) {
				// do nothing
			} else if (succCont.getReachProp() == mRpSomeDown) {
				for (final STATE down : succCont.getDownStates().keySet()) {
					if (succCont.hasDownProp(down, mDspReachPrecious)
							|| succCont.hasDownProp(down, mDspReachableAfterRemoval)) {
						// do nothing
					} else {
						// check if we can propagate some down state
						if (cont.getDownStates().containsKey(down)) {
							if (cont.getReachProp() == mRpAllDown) {
								modified |= succCont.setDownProp(down, mDspReachableAfterRemoval);
							} else {
								if (cont.hasDownProp(down, mDspReachPrecious)
										|| cont.hasDownProp(down, mDspReachableAfterRemoval)) {
									modified |= succCont.setDownProp(down, mDspReachableAfterRemoval);
								} else {
									// DoubleDecker (cont,down) has neither
									// mDspReachPrecious nor
									// mDspReachableAfterRemoval property
								}
							}

						}
					}
				}
			} else {
				throw new AssertionError("succ will be removed");
			}
			return modified;
		}

		/*
		 * private void addToWorklistIfNotAlreadyVisited(ArrayDeque<StateContainer<LETTER, STATE>> propagationWorklist,
		 * Set<StateContainer<LETTER, STATE>> visited, StateContainer<LETTER, STATE> succCont) { boolean alreadyVisited
		 * = visited.contains(succCont); if (!alreadyVisited) { propagationWorklist.add(succCont);
		 * visited.add(succCont); } // return alreadyVisited; }
		 */

		/**
		 * FIXME: documentation incorrect
		 * @param upState
		 *            up state
		 * @param downState
		 *            down state
		 * @return true iff the DoubleDecker (up,down) is reachable in the original automaton (before removal of
		 *         deadEnds or non-live states). This is a workaround to maintain backward compatibility with the old
		 *         implementation. In the future we return true if (up,down) is reachable in the resulting automaton
		 */
		public boolean isDownState(final STATE upState, final STATE downState, final DoubleDeckerReachability ddr) {
			final StateContainer<LETTER, STATE> cont = getStatesMap().get(upState);
			assert cont.getReachProp() == mRpAllDown || cont.getReachProp() == mRpSomeDown;
			if (cont.getDownStates().containsKey(downState)) {
				if (cont.getReachProp() == mRpAllDown) {
					assert cont.getDownStates().containsKey(downState);
					return true;
				}
				assert cont.getReachProp() == mRpSomeDown;
				final boolean canReachPrecious = cont.hasDownProp(downState, mDspReachPrecious);
				switch (ddr) {
				case CAN_REACH_PRECIOUS: {
					return canReachPrecious;
				}
				case REACHABLE_AFTER_REMOVAL_OF_PRECIOUS_NOT_REACHERS: {
					final boolean notRemoved = canReachPrecious
							|| cont.hasDownProp(downState, mDspReachableAfterRemoval);
					return notRemoved;
				}
				default:
					throw new AssertionError();
				}
			}
			return false;
		}

		/**
		 * FIXME: documentation incorrect
		 * @param state
		 *            up state
		 * @return The set of all down states such that (up,down) is reachable DoubleDecker in original automaton
		 *         (before removal of deadEnds or non-live states). This is a workaround to maintain backward
		 *         compatibility with the old implementation. In the future we return set of down states in resulting
		 *         automaton.
		 */
		public Set<STATE> getDownStates(final STATE state, final DoubleDeckerReachability ddr) {
			final StateContainer<LETTER, STATE> cont = getStatesMap().get(state);
			// return cont.getDownStates().keySet();
			Set<STATE> downStates;
			if (cont.getReachProp() == mRpAllDown) {
				downStates = cont.getDownStates().keySet();
			} else {
				assert cont.getReachProp() == mRpSomeDown;
				downStates = new HashSet<>();
				for (final STATE downState : cont.getDownStates().keySet()) {
					final boolean canReachPrecious = cont.hasDownProp(downState, mDspReachPrecious);
					switch (ddr) {
					case CAN_REACH_PRECIOUS: {
						if (canReachPrecious) {
							downStates.add(downState);
						}
						break;
					}
					case REACHABLE_AFTER_REMOVAL_OF_PRECIOUS_NOT_REACHERS: {
						final boolean notRemoved = canReachPrecious
								|| cont.hasDownProp(downState, mDspReachableAfterRemoval);
						if (notRemoved) {
							downStates.add(downState);
						}
						break;
					}
					default:
						throw new AssertionError();
					}
				}
			}

			/*
			 * for (Entry<LETTER, STATE> entry : getStatesMap().get(up).getCommonEntriesComponent().getEntries()) {
			 * STATE entryState = entry.getState(); for (IncomingCallTransition<LETTER, STATE> trans :
			 * callPredecessors(entryState)) { STATE callPred = trans.getPred(); StateContainer<LETTER, STATE>
			 * callPredCont = getStatesMap().get(callPred); if (callPredCont.getReachProp() != ReachProp.REACHABLE) {
			 * downStates.add(callPred); } } if (getInitialStatesPrivate()AfterDeadEndRemoval.contains(entryState)) {
			 * downStates.add(getEmptyStackState()); } }
			 */
			return downStates;
		}

		/**
		 * @param state
		 *            A state.
		 * @return true if the DoubleDecker (state,auxiliaryEmptyStackState) can reach a precious state (finals
		 *         DeadEndComputation, accepting SSCs in non-live computation)
		 */
		public boolean isInitial(final STATE state) {
			if (!getInitialStatesPrivate().contains(state)) {
				throw new IllegalArgumentException("Not initial state");
			}
			final StateContainer<LETTER, STATE> cont = getStatesMap().get(state);
			if (cont.getReachProp() == mRpAllDown) {
				// assert cont.getDownStates().get(getEmptyStackState()) == ReachProp.REACHABLE;
				return true;
			}
			return cont.hasDownProp(getEmptyStackState(), mDspReachPrecious);
		}

		/**
		 * @return All triples (up,down,entry) such that from the DoubleDecker (up,down) the starting states of this
		 *         ancestor computation (e.g., final states in dead end computation) is reachable. This is a workaround
		 *         to maintain backward compatibility. In the future we return triples reachable in resulting automaton.
		 */
		public Iterable<UpDownEntry<STATE>> getRemovedUpDownEntry() {
			return () -> new Iterator<UpDownEntry<STATE>>() {
				private Iterator<STATE> mUpIterator;
				private STATE mUp;
				private Iterator<STATE> mDownIterator;
				private STATE mDown;
				private boolean mHasNext = true;
				private StateContainer<LETTER, STATE> mStateContainer;

				{
					mUpIterator = getStatesMap().keySet().iterator();
					if (mUpIterator.hasNext()) {
						mUp = mUpIterator.next();
						mStateContainer = getStatesMap().get(mUp);
						mDownIterator = mStateContainer.getDownStates().keySet().iterator();
					} else {
						mHasNext = false;
					}
					computeNextElement();

				}

				private void computeNextElement() {
					mDown = null;
					while (mDown == null && mHasNext) {
						if (mStateContainer.getReachProp() != mRpAllDown && mDownIterator.hasNext()) {
							final STATE downCandidate = mDownIterator.next();
							if (mStateContainer.getReachProp() == ReachProp.REACHABLE) {
								mDown = downCandidate;
							} else {
								assert mStateContainer.getReachProp() == mRpSomeDown;
								if (!mStateContainer.hasDownProp(downCandidate, mDspReachPrecious)) {
									mDown = downCandidate;
								}
							}
						} else if (mUpIterator.hasNext()) {
							mUp = mUpIterator.next();
							mStateContainer = getStatesMap().get(mUp);
							mDownIterator = mStateContainer.getDownStates().keySet().iterator();
						} else {
							mHasNext = false;
						}
					}
				}

				@Override
				public boolean hasNext() {
					return mHasNext;
				}

				@Override
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
						assert checkStateEquality(mDown, getEmptyStackState());
					}
					final UpDownEntry<STATE> result = new UpDownEntry<>(mUp, mDown, entry);
					computeNextElement();
					return result;
				}

				@Override
				public void remove() {
					throw new UnsupportedOperationException();
				}
			};
		}

		/**
		 * Compute call successors for a given set of states.
		 */
		Set<STATE> computeState2CallSuccs(final STATE state) {
			final Set<STATE> callSuccs = new HashSet<>();
			if (!checkStateEquality(state, getEmptyStackState())) {
				for (final OutgoingCallTransition<LETTER, STATE> trans : callSuccessors(state)) {
					callSuccs.add(trans.getSucc());
				}
			}
			return callSuccs;
		}
	}

	// //////////////////////////////////////////////////////////////////////////

	/**
	 * Detect which summaries are accepting. Find states q and q' such that q' is reachable from q via a run that
	 * <ul>
	 * <li>starts with a call
	 * <li>ends with a return
	 * <li>contains an accepting state
	 * </ul>
	 * The resulting map has call predecessors in its keySet and sets of return successors in its values.
	 */
	class AcceptingSummariesComputation {
		private final ArrayDeque<StateContainer<LETTER, STATE>> mFinAncWorklist = new ArrayDeque<>();
		private final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> mAcceptingSummariesInner =
				new HashRelation<>();

		public AcceptingSummariesComputation() {
			init();
			while (!mFinAncWorklist.isEmpty()) {
				final StateContainer<LETTER, STATE> cont = mFinAncWorklist.removeFirst();
				propagateNewDownStates(cont);
			}
		}

		public HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> getAcceptingSummaries() {
			return mAcceptingSummariesInner;
		}

		private void init() {
			for (final STATE fin : getFinalStatesPrivate()) {
				final StateContainer<LETTER, STATE> cont = getStatesMap().get(fin);
				addNewDownStates(null, cont, cont.getDownStates().keySet());
			}
		}

		private void addNewDownStates(final StateContainer<LETTER, STATE> cont,
				final StateContainer<LETTER, STATE> succCont, final Set<STATE> potentiallyNewDownStates) {
			if (checkStateContainerEquality(cont, succCont)) {
				return;
			}
			boolean newDownStateWasPropagated = false;
			for (final STATE down : potentiallyNewDownStates) {
				final boolean modified = succCont.setDownProp(down, DownStateProp.REACHABLE_FROM_FINAL_WITHOUT_CALL);
				if (modified) {
					newDownStateWasPropagated = true;
				}
			}
			if (newDownStateWasPropagated) {
				mFinAncWorklist.add(succCont);
			}
		}

		private void propagateNewDownStates(final StateContainer<LETTER, STATE> cont) {
			final Set<STATE> unpropagatedDownStates = cont.getUnpropagatedDownStates();
			if (unpropagatedDownStates == null) {
				return;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> trans : cont.internalSuccessors()) {
				final StateContainer<LETTER, STATE> succCont = getStatesMap().get(trans.getSucc());
				addNewDownStates(cont, succCont, unpropagatedDownStates);
			}
			for (final SummaryReturnTransition<LETTER, STATE> trans : summarySuccessors(cont.getState())) {
				final StateContainer<LETTER, STATE> succCont = getStatesMap().get(trans.getSucc());
				addNewDownStates(cont, succCont, unpropagatedDownStates);
			}
			cont.eraseUnpropagatedDownStates();
			for (final OutgoingReturnTransition<LETTER, STATE> trans : cont.returnSuccessors()) {
				final StateContainer<LETTER, STATE> hierCont = getStatesMap().get(trans.getHierPred());
				final StateContainer<LETTER, STATE> succCont = getStatesMap().get(trans.getSucc());
				final STATE hierPred = trans.getHierPred();
				if (cont.hasDownProp(hierPred, DownStateProp.REACHABLE_FROM_FINAL_WITHOUT_CALL)) {
					addNewDownStates(null, succCont, hierCont.getDownStates().keySet());
					addAcceptingSummary(hierCont, cont, trans.getLetter(), succCont);
				}
			}
		}

		private void addAcceptingSummary(final StateContainer<LETTER, STATE> callPred,
				final StateContainer<LETTER, STATE> returnPred, final LETTER letter,
				final StateContainer<LETTER, STATE> returnSucc) {
			final Summary<LETTER, STATE> summary = new Summary<>(callPred, returnPred, letter, returnSucc);
			mAcceptingSummariesInner.addPair(callPred, summary);
		}
	}

	/*
	 * private boolean cecSumConsistent() { int sum = 0; for (CommonEntriesComponent<LETTER, STATE> cec : mAllCECs) {
	 * sum += cec.mSize; } int allStates = getStatesMap().keySet().size(); return sum == allStates; }
	 *
	 * private boolean allStatesAreInTheirCec() { boolean result = true; for (STATE state : getStatesMap().keySet()) {
	 * StateContainer<LETTER, STATE> sc = getStatesMap().get(state); CommonEntriesComponent<LETTER, STATE> cec =
	 * sc.getCommonEntriesComponent(); if (!cec.mBorderOut.keySet().contains(sc)) { Set<StateContainer<LETTER, STATE>>
	 * empty = new HashSet<StateContainer<LETTER, STATE>>(); result &= internalOutSummaryOutInCecOrForeigners(sc, empty,
	 * cec); } } return result; }
	 *
	 * private boolean occuringStatesAreConsistent(CommonEntriesComponent<LETTER, STATE> cec) { boolean result = true;
	 * Set<STATE> downStates = cec.mDownStates; Set<Entry<LETTER, STATE>> entries = cec.mEntries; if (cec.mSize > 0) {
	 * result &= downStatesAreCallPredsOfEntries(downStates, entries); } assert (result); result &=
	 * eachStateHasThisCec(cec.getReturnOutCandidates(), cec); assert (result); for (StateContainer<LETTER, STATE>
	 * resident : cec.mBorderOut.keySet()) { Set<StateContainer<LETTER, STATE>> foreignerSCs =
	 * cec.mBorderOut.get(resident); result &= internalOutSummaryOutInCecOrForeigners(resident, foreignerSCs, cec);
	 * assert (result); } return result; }
	 *
	 * private boolean downStatesConsistentwithEntriesDownStates(CommonEntriesComponent<LETTER, STATE> cec) { boolean
	 * result = true; Set<STATE> downStates = cec.mDownStates; Set<Entry<LETTER, STATE>> entries = cec.mEntries;
	 * Set<STATE> downStatesofEntries = new HashSet<STATE>(); for (Entry<LETTER, STATE> entry : entries) {
	 * downStatesofEntries.addAll(entry.getDownStates().keySet()); } result &= isSubset(downStates,
	 * downStatesofEntries); assert (result); result &= isSubset(downStatesofEntries, downStates); assert (result);
	 * return result; }
	 *
	 * private boolean internalOutSummaryOutInCecOrForeigners(StateContainer<LETTER, STATE> state,
	 * Set<StateContainer<LETTER, STATE>> foreigners, CommonEntriesComponent<LETTER, STATE> cec) {
	 * Set<StateContainer<LETTER, STATE>> neighbors = new HashSet<StateContainer<LETTER, STATE>>();
	 *
	 * for (OutgoingInternalTransition<LETTER, STATE> trans : state.internalSuccessors()) { STATE succ =
	 * trans.getSucc(); StateContainer<LETTER, STATE> succSc = getStatesMap().get(succ); if
	 * (succSc.getCommonEntriesComponent() == cec) { // do nothing } else { neighbors.add(succSc); } } if
	 * (mSummaries.containsKey(state)) { for (StateContainer<LETTER, STATE> succSc : mSummaries.get(state)) { if
	 * (succSc.getCommonEntriesComponent() == cec) { // do nothing } else { neighbors.add(succSc); } } } boolean
	 * allNeighborAreForeigners = isSubset(neighbors, foreigners); assert allNeighborAreForeigners; boolean
	 * allForeignersAreNeighbor = isSubset(foreigners, neighbors); assert allForeignersAreNeighbor; return
	 * allNeighborAreForeigners && allForeignersAreNeighbor; }
	 *
	 * private boolean eachStateHasThisCec(Set<STATE> states, CommonEntriesComponent<LETTER, STATE> cec) { boolean
	 * result = true; for (STATE state : states) { StateContainer<LETTER, STATE> sc = getStatesMap().get(state); if
	 * (sc.getCommonEntriesComponent() != cec) { result = false; assert result; } } return result; }
	 *
	 * private boolean downStatesAreCallPredsOfEntries(Set<STATE> downStates, Set<Entry<LETTER, STATE>> entries) {
	 * Set<STATE> callPreds = new HashSet<STATE>(); for (Entry<LETTER, STATE> entry : entries) { STATE entryState =
	 * entry.getState(); if (isInitial(entryState)) { callPreds.add(getEmptyStackState()); } for
	 * (IncomingCallTransition<LETTER, STATE> trans : callPredecessors(entryState)) { callPreds.add(trans.getPred()); }
	 * } boolean callPredsIndownStates = isSubset(callPreds, downStates); assert (callPredsIndownStates); boolean
	 * downStatesInCallPreds = isSubset(downStates, callPreds); assert (downStatesInCallPreds); return
	 * callPredsIndownStates && downStatesInCallPreds; }
	 *
	 * private boolean isBorderOutConsistent(StateContainer<LETTER, STATE> cont) { CommonEntriesComponent<LETTER, STATE>
	 * cec = cont.getCommonEntriesComponent(); ArrayList<STATE> preds = new ArrayList<STATE>(); for
	 * (IncomingInternalTransition<LETTER, STATE> inTrans : internalPredecessors(cont.getState())) {
	 * preds.add(inTrans.getPred()); } for (IncomingReturnTransition<LETTER, STATE> inTrans :
	 * returnPredecessors(cont.getState())) { preds.add(inTrans.getHierPred()); } boolean result = true; for (STATE pred
	 * : preds) { StateContainer<LETTER, STATE> predCont = getStatesMap().get(pred); if
	 * (predCont.getCommonEntriesComponent() != cec) { if
	 * (predCont.getCommonEntriesComponent().mBorderOut.containsKey(predCont)) { Set<StateContainer<LETTER, STATE>>
	 * foreigners = predCont.getCommonEntriesComponent().mBorderOut.get(predCont); result &= foreigners.contains(cont);
	 * } else { result = false; } assert result; } else { if
	 * (predCont.getCommonEntriesComponent().mBorderOut.containsKey(predCont)) { Set<StateContainer<LETTER, STATE>>
	 * foreigners = predCont.getCommonEntriesComponent().mBorderOut.get(predCont); result &= !foreigners.contains(cont);
	 * assert result; } } } return result; }
	 */
}
