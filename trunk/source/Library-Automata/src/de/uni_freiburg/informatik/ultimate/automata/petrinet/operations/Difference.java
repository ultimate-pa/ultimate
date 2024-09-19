/*
 * Copyright (C) 2011-2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.PetriNetUtils;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Computes the difference L(N)-(L(A)◦Σ^*) between a {@link BoundedPetriNet} N and an {@link INestedWordAutomaton} A.
 * This operation supports only subtrahend automata with the following properties. Results for other subtrahend automata
 * may or may not be correct.
 * <p>
 * Properties of the subtrahend automata A:
 * <ul>
 * <li>Subtrahend is a deterministic finite automaton (DFA)
 * <ul>
 * <li>There is exactly one initial state
 * <li>For every state and letter there is at most one outgoing edge.
 * </ul>
 * <li>For every minuend word uv ∈ L(N)
 * <ul>
 * <li>there is an explicit run in A consuming the whole word uv
 * <li>or u ∈ L(A).
 * </ul>
 * </ul>
 * <p>
 * If the subtrahend automaton A is closed under concatenation with Σ^* then L(A)◦Σ^* = L(A) and therefore
 * L(N)-(L(A)◦Σ^*) = L(N)-L(A); in other words: The result of this operation is the normal difference.
 *
 * TODO 2019-10-15 Matthias: Allow user to specify set of universal loopers.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author schaetzc@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 *            Type of letters in the alphabet of minuend Petri net, subtrahend DFA, and difference Petri net
 * @param <PLACE>
 *            Type of places in minuend and difference Petri net
 * @param <CRSF>
 *            Type of factory needed to check the result of this operation in {@link #checkResult(CRSF)}
 */
public final class Difference<LETTER, PLACE, CRSF extends IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
		extends GeneralOperation<LETTER, PLACE, CRSF> {

	/**
	 * Synchronization with self-loops in subtrahend DFA can be done using different methods. In theory, the
	 * synchronization method can be chosen per self-loop. The synchronization methods listed here are used for all
	 * self-loops. However, some of the synchronization methods may decide per self-loop how to synchronize.
	 */
	public enum LoopSyncMethod {
		/**
		 * Synchronize with each LETTER-self-loop in subtrahend DFA by inserting a transition for each LETTER-transition
		 * in the minuend Petri net.
		 */
		PAIRWISE,
		/**
		 * Synchronize with all LETTER-self-loops in subtrahend DFA by inserting a single transition for all
		 * LETTER-transition in the minuend Petri net together. The new transition checks that the subtrahend DFA is not
		 * in a LETTER-changer state (a state that can be left by reading LETTER) by checking black places of said
		 * changer states.
		 */
		INVERTED,
		/**
		 * For each LETTER decide whether to use {@link #PAIRWISE} or {@link #INVERTED} trying to minimize the resulting
		 * difference Petri net using a heuristic.
		 */
		HEURISTIC,
	}

	/**
	 * If we have have full information about self-loop (which is the case if information about loopers and changers is
	 * not provided by the user) and there is no self-loop (in the DFA) for transition then we can omit the inverted
	 * synchronization for this transition
	 */
	private static final boolean FULL_SELFLOOP_INFORMATION_OPTIMIZATION = false;

	private static final boolean COMPUTE_DIFFERENCE_SYNCHRONIZATION_INFORMATION_VIA_UNFOLDING = true;

	private final LoopSyncMethod mLoopSyncMethod;

	/**
	 * If true, we apply our {@link RemoveRedundantFlow} operation to the on-demand computed preliminary difference. We
	 * take all information about redundant, and update the {@link DifferenceSynchronizationInformation} accordingly and
	 * obtain a result where some redundant flow is removed.
	 */
	private final boolean mRemoveRedundantFlow;

	private final IPetriNet<LETTER, PLACE> mInputMinuend;
	private final IPetriNet<LETTER, PLACE> mMinuend;
	private final INestedWordAutomaton<LETTER, PLACE> mSubtrahend;
	private final IBlackWhiteStateFactory<PLACE> mContentFactory;

	private BoundedPetriNet<LETTER, PLACE> mResult;

	private final DifferenceSynchronizationInformation<LETTER, PLACE> mDsi;

	private final Map<PLACE, PLACE> mWhitePlace = new HashMap<>();
	private final Map<PLACE, PLACE> mBlackPlace = new HashMap<>();

	public Difference(final AutomataLibraryServices services, final IBlackWhiteStateFactory<PLACE> factory,
			final IPetriNet<LETTER, PLACE> minuendNet, final INestedWordAutomaton<LETTER, PLACE> subtrahendDfa)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		this(services, factory, minuendNet, subtrahendDfa, LoopSyncMethod.HEURISTIC, null, false);
	}

	public Difference(final AutomataLibraryServices services, final IBlackWhiteStateFactory<PLACE> factory,
			final IPetriNet<LETTER, PLACE> minuendNet, final INestedWordAutomaton<LETTER, PLACE> subtrahendDfa,
			final String loopSyncMethod) throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		this(services, factory, minuendNet, subtrahendDfa, LoopSyncMethod.valueOf(loopSyncMethod), null, false);
	}

	public Difference(final AutomataLibraryServices services, final IBlackWhiteStateFactory<PLACE> factory,
			final IPetriNet<LETTER, PLACE> originalMinuend, final INestedWordAutomaton<LETTER, PLACE> subtrahendDfa,
			final LoopSyncMethod loopSyncMethod, final DifferencePairwiseOnDemand<LETTER, PLACE, ?> inputDpod,
			final boolean removeRedundantFlow) throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services);
		if (DataStructureUtils.haveNonEmptyIntersection(originalMinuend.getPlaces(), subtrahendDfa.getStates())) {
			throw new UnsupportedOperationException(
					"Difference is only supported for operands with distinct places / states.");
		}
		mSubtrahend = subtrahendDfa;
		mContentFactory = factory;
		mLoopSyncMethod = loopSyncMethod;
		mInputMinuend = originalMinuend;
		mRemoveRedundantFlow = removeRedundantFlow;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		assert checkSubtrahendProperties();

		final DifferencePairwiseOnDemand<LETTER, PLACE, ?> dpod;
		if (inputDpod == null && COMPUTE_DIFFERENCE_SYNCHRONIZATION_INFORMATION_VIA_UNFOLDING) {
			dpod = new DifferencePairwiseOnDemand<>(mServices, originalMinuend, subtrahendDfa);
		} else {
			dpod = inputDpod;
		}
		if (!COMPUTE_DIFFERENCE_SYNCHRONIZATION_INFORMATION_VIA_UNFOLDING) {
			if (mRemoveRedundantFlow) {
				throw new UnsupportedOperationException("Cannot remove rundundant flow without finite prefix.");
			}
			mMinuend = originalMinuend;
			mDsi = new DifferenceSynchronizationInformation<>(new HashSet<>(), new HashRelation<>(),
					new HashRelation<>(), new HashSet<>(mMinuend.getTransitions()), new HashRelation<>(), false, false);
			partitionStates();
		} else if (mRemoveRedundantFlow) {
			final RemoveRedundantFlow<LETTER, PLACE, ?> rrf = new RemoveRedundantFlow<>(mServices, dpod.getResult(),
					dpod.getFinitePrefixOfDifference().getResult(), mInputMinuend.getPlaces(),
					mInputMinuend.getPlaces());
			final ProjectToSubnet<LETTER, PLACE> pts =
					new ProjectToSubnet<>(services, rrf.getResult(), new HashRelation<>(), mSubtrahend.getStates());
			mMinuend = pts.getResult();
			final HashRelation<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> minuendTransition2differenceTransitions =
					new HashRelation<>();
			for (final Entry<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> entry : dpod
					.getTransitionBacktranslation().entrySet()) {
				final Transition<LETTER, PLACE> diffTransition = entry.getKey();
				assert diffTransition != null;
				minuendTransition2differenceTransitions.addPair(entry.getValue(), diffTransition);
			}
			final Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> differenceTransitions2projectedTransitions =
					new HashMap<>();
			for (final Entry<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> entry : rrf.getOld2projected()
					.entrySet()) {
				final Transition<LETTER, PLACE> diffTransition = entry.getKey();
				final Transition<LETTER, PLACE> rrfTransition = entry.getValue();
				assert rrfTransition != null;
				final Transition<LETTER, PLACE> projTransition = pts.getTransitionMapping().get(rrfTransition);
				assert projTransition != null;
				differenceTransitions2projectedTransitions.put(diffTransition, projTransition);
			}
			mDsi = dpod.getDifferenceSynchronizationInformation().transformThroughRemoveRedundantFlow(
					minuendTransition2differenceTransitions, differenceTransitions2projectedTransitions,
					rrf.getRedundantSelfloopFlow(), rrf.getRedundantPlaces());
		} else {
			mMinuend = originalMinuend;
			mDsi = dpod.getDifferenceSynchronizationInformation();
		}
		assert mDsi.isCompatible(mMinuend) : "incompatible DSI";
		copyNetPlaces();
		addBlackAndWhitePlaces();
		addTransitions();
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	private boolean checkSubtrahendProperties() {
		if (!NestedWordAutomataUtils.isFiniteAutomaton(mSubtrahend)) {
			throw new IllegalArgumentException("subtrahend must be a finite automaton");
		} else if (!IAutomaton.sameAlphabet(mInputMinuend, mSubtrahend)) {
			// not really necessary, but different alphabets could be hinting at bugs in other operations
			throw new IllegalArgumentException("minuend and subtrahend must use same alphabet");
		} else if (mSubtrahend.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("subtrahend must have exactly one inital state");
		}
		// omitted check: Reachable transitions from minuend have sync partners in subtrahend
		// omitted check: subtrahend has to be deterministic
		return true;
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName() + ". First operand " + mInputMinuend.sizeInformation()
				+ ". Second operand " + mSubtrahend.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mResult.sizeInformation();
	}

	private void partitionStates() {
		for (final Transition<LETTER, PLACE> transition : mMinuend.getTransitions()) {
			final Set<PLACE> selfloopStates = new HashSet<>();
			final Set<PLACE> changerStates = new HashSet<>();
			for (final PLACE state : mSubtrahend.getStates()) {
				if (mSubtrahend.isFinal(state)) {
					// final states and their outgoing transitions are not copied to the result
					// because we compute L(N)-(L(A)◦∑^*). Once a final state in the subtrahend A is reached,
					// the difference cannot accept anymore.
					continue;
				}
				final OutgoingInternalTransition<LETTER, PLACE> successors =
						atMostOneElement(mSubtrahend.internalSuccessors(state, transition.getSymbol()));
				if (successors == null) {
					continue;
				} else if (successors.getSucc().equals(state)) {
					selfloopStates.add(state);
				} else {
					changerStates.add(state);
				}
			}
			mDsi.getSelfloops().addAllPairs(transition, selfloopStates);
			mDsi.getStateChangers().addAllPairs(transition, changerStates);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(transition + " has " + selfloopStates.size() + " selfloop and " + changerStates.size()
						+ " changer(s)");
			}
		}
		final int changers = (int) mDsi.getStateChangers().getDomain().stream()
				.filter(x -> !mDsi.getStateChangers().getImage(x).isEmpty()).count();
		mLogger.info((mMinuend.getAlphabet().size() - changers) + " loopers, " + changers + " changers");
	}

	private void copyNetPlaces() {
		// the correct "constantTokenAmmount" could be computed after "addBlackAndWhitePlaces()" using ...
		// mOperand.constantTokenAmount() && mBlackPlace.size() == mWhitePlace.size()
		// ... but field "constantTokenAmmount" has to be set in constructor and cannot be changed afterwards.
		final boolean constantTokenAmount = false;
		mResult = new BoundedPetriNet<>(mServices, mMinuend.getAlphabet(), constantTokenAmount);
		final boolean initialStateIsFinal = isInitialStateFinal();

		for (final PLACE oldPlace : mMinuend.getPlaces()) {
			final boolean isInitial = !initialStateIsFinal && mMinuend.getInitialPlaces().contains(oldPlace);
			final boolean isAccepting = mMinuend.getAcceptingPlaces().contains(oldPlace);
			final boolean newlyAdded = mResult.addPlace(oldPlace, isInitial, isAccepting);
			if (!newlyAdded) {
				throw new AssertionError("Must not add place twice: " + oldPlace);
			}
		}
	}

	private boolean isInitialStateFinal() {
		final Iterator<PLACE> it = mSubtrahend.getInitialStates().iterator();
		if (!it.hasNext()) {
			throw new UnsupportedOperationException(
					"Subtrahend has no initial states! We could soundly return the minuend as result (implement this if required). "
							+ "However we presume that in most cases, such a subtrahend was passed accidentally");
		}
		final PLACE automatonInitialState = it.next();
		if (it.hasNext()) {
			throw new IllegalArgumentException("subtrahend not deterministic");
		}
		return mSubtrahend.isFinal(automatonInitialState);
	}

	/**
	 * Heuristic for choosing a synchronization method for all transitions with a given letter.
	 *
	 * @param oldTrans
	 *            Label of transitions to be synchronized.
	 * @return Use {@link #syncWithAnySelfloop(Transition)}, else use {@link #syncWithEachSelfloop(Transition)}
	 */
	private boolean invertSyncWithSelfloops(final Transition<LETTER, PLACE> oldTrans) {
		return mLoopSyncMethod == LoopSyncMethod.INVERTED || (mLoopSyncMethod == LoopSyncMethod.HEURISTIC
				&& mDsi.getSelfloops().getImage(oldTrans).size() >= mDsi.getStateChangers().getImage(oldTrans).size())
				|| (mLoopSyncMethod == LoopSyncMethod.PAIRWISE
						&& !mDsi.getChangerLetters().contains(oldTrans.getSymbol()));
	}

	private Set<PLACE> requiredBlackPlaces() {
		final Set<PLACE> requiredBlack = new HashSet<>();
		for (final Transition<LETTER, PLACE> oldTrans : mDsi.getContributingTransitions()) {
			if (invertSyncWithSelfloops(oldTrans)) {
				requiredBlack.addAll(mDsi.getStateChangers().getImage(oldTrans));
				requiredBlack.addAll(mDsi.getBlockingTransitions().getImage(oldTrans));
			}
		}
		return requiredBlack;
	}

	private void addBlackAndWhitePlaces() {
		for (final PLACE state : mSubtrahend.getStates()) {
			if (mSubtrahend.isFinal(state)) {
				continue;
			}
			final boolean isInitial = mSubtrahend.getInitialStates().contains(state);
			final PLACE whitePlace = mContentFactory.getWhiteContent(state);
			final boolean newlyAdded = mResult.addPlace(whitePlace, isInitial, false);
			if (!newlyAdded) {
				throw new UnsupportedOperationException(
						"Cannot add place " + whitePlace + " maybe you have to rename your input.");
			}
			mWhitePlace.put(state, whitePlace);
		}
		for (final PLACE state : requiredBlackPlaces()) {
			final boolean isInitial = mSubtrahend.getInitialStates().contains(state);
			final PLACE blackPlace = mContentFactory.getBlackContent(state);
			final boolean newlyAdded = mResult.addPlace(blackPlace, !isInitial, false);
			if (!newlyAdded) {
				throw new UnsupportedOperationException(
						"Cannot add place " + blackPlace + " maybe you have to rename your input.");
			}
			mBlackPlace.put(state, blackPlace);
		}
	}

	private void addTransitions() {
		for (final Transition<LETTER, PLACE> oldTrans : mDsi.getContributingTransitions()) {
			assert mMinuend.getTransitions().contains(oldTrans) : "unknown transition " + oldTrans;
			for (final PLACE predState : mDsi.getStateChangers().getImage(oldTrans)) {
				syncWithChanger(oldTrans, predState);
			}
			syncWithSelfloops(oldTrans);
		}
	}

	private void syncWithChanger(final Transition<LETTER, PLACE> oldTrans, final PLACE predState) {
		final PLACE succState = onlyElement(mSubtrahend.internalSuccessors(predState, oldTrans.getSymbol())).getSucc();
		assert !predState.equals(succState) : "changer requires that pred and succ are different";
		if (mSubtrahend.isFinal(succState)) {
			// optimization for special structure of subtrahend automata L(A)◦Σ^*:
			// omit this transition because subtrahend will accept everything afterwards
			return;
		}
		final Set<PLACE> predecessors = new HashSet<>();
		final Set<PLACE> successors = new HashSet<>();
		predecessors.add(mWhitePlace.get(predState));
		successors.add(mWhitePlace.get(succState));
		final PLACE blackPred = mBlackPlace.get(succState);
		final PLACE blackSucc = mBlackPlace.get(predState);
		if (blackPred != null) {
			predecessors.add(blackPred);
		}
		if (blackSucc != null) {
			successors.add(blackSucc);
		}
		predecessors.addAll(oldTrans.getPredecessors());
		successors.addAll(oldTrans.getSuccessors());
		mResult.addTransition(oldTrans.getSymbol(), ImmutableSet.of(predecessors), ImmutableSet.of(successors));
	}

	private void syncWithSelfloops(final Transition<LETTER, PLACE> oldTrans) {
		if (invertSyncWithSelfloops(oldTrans)) {
			// If we have to process this transition (e.g., because it occurs as blocking
			// transition) we may enter this if-branch even if there are 0 self-loops (e.g.,
			// because we have 0 selfloops and 0 changers). However, we must not add a "0
			// self-loop" transition because it would be unreachable.
			if (mDsi.getSelfloops().getImage(oldTrans).isEmpty()
					&& mDsi.getChangerLetters().contains(oldTrans.getSymbol())) {
				// do nothing
			} else {
				syncWithAnySelfloop(oldTrans);
			}
		} else {
			syncWithEachSelfloop(oldTrans);
		}
	}

	/**
	 * Synchronizes a transition from the minuend Petri net with all related transitions of the subtrahend automaton.
	 * Synchronization is done the same way as synchronization with changers. For every transition in the subtrahend
	 * automaton a transition is inserted in the result.
	 * <p>
	 * Pros:
	 * <ul>
	 * <li>No black places needed
	 * <li>Inserted transitions have low degree
	 * </ul>
	 * Cons:
	 * <ul>
	 * <li>Inserts multiple transitions, one per sync partner
	 * </ul>
	 * This approach is optimized for cases in which the subtrahend automaton has only few selfloops (with the same
	 * symbol as the transition to be synchronized).
	 *
	 * @param oldTrans
	 *            Minuend's transition to be synchronized with subtrahend
	 *
	 * @see #invertSyncWithSelfloops(LETTER)
	 */
	private void syncWithEachSelfloop(final Transition<LETTER, PLACE> oldTrans) {
		// Relies on the special properties of the subtrahend L(A)◦Σ^*.
		for (final PLACE state : mDsi.getSelfloops().getImage(oldTrans)) {
			final PLACE wPlace = mWhitePlace.get(state);
			if (wPlace == null) {
				throw new AssertionError("No black place for " + state);
			}
			final Set<PLACE> predecessors = new HashSet<>();
			final Set<PLACE> successors = new HashSet<>();
			predecessors.add(wPlace);
			predecessors.addAll(oldTrans.getPredecessors());
			successors.add(wPlace);
			successors.addAll(oldTrans.getSuccessors());
			mResult.addTransition(oldTrans.getSymbol(), ImmutableSet.of(predecessors), ImmutableSet.of(successors));
		}
	}

	/**
	 * Synchronizes a transition from the minuend Petri net with all related transitions of the subtrahend automaton
	 * inserting just one new transition into the resulting difference Petri net. Instead of checking that the
	 * subtrahend automaton is in any selfloop state, checks that the subtrahen automaton is not in any other state.
	 * <p>
	 * Pros:
	 * <ul>
	 * <li>One transition, no matter how many sync partners
	 * </ul>
	 * Cons:
	 * <ul>
	 * <li>Needs Black places for every non-sync partner
	 * <li>Inserted transition may have a very high degree
	 * </ul>
	 * This approach is optimized for cases in which the subtrahend automaton has a selfloop (with the same symbol as
	 * the transition to be synchronized) on nearly all of its states.
	 *
	 * @param oldTrans
	 *            Minuend's transition to be synchronized with subtrahend
	 *
	 * @see #invertSyncWithSelfloops(LETTER)
	 */
	private void syncWithAnySelfloop(final Transition<LETTER, PLACE> oldTrans) {
		if (FULL_SELFLOOP_INFORMATION_OPTIMIZATION && mDsi.getSelfloops().getImage(oldTrans).isEmpty()) {
			// This optimization relies on the special properties of the subtrahend L(A)◦Σ^*.
			return;
		}
		final Set<PLACE> predecessors = new HashSet<>(oldTrans.getPredecessors());
		final Set<PLACE> successors = new HashSet<>(oldTrans.getSuccessors());
		for (final PLACE state : Stream.concat(mDsi.getStateChangers().getImage(oldTrans).stream(),
				mDsi.getBlockingTransitions().getImage(oldTrans).stream()).collect(Collectors.toList())) {
			final PLACE bPlace = mBlackPlace.get(state);
			if (bPlace == null) {
				throw new AssertionError("No black place for " + state);
			}
			predecessors.add(bPlace);
			successors.add(bPlace);
		}
		mResult.addTransition(oldTrans.getSymbol(), ImmutableSet.of(predecessors), ImmutableSet.of(successors));
	}

	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of " + getOperationName());
		}

		boolean correct =
				PetriNetUtils.doDifferenceLanguageCheck(mServices, stateFactory, mMinuend, mSubtrahend, mResult);

		if (correct) {
			if (mDsi.isReachabilityPreserved()) {
				final int unreachableTransitionsMinuend = computeNumberOfUnreachableTransitions(mMinuend, mServices);
				if (unreachableTransitionsMinuend == 0) {
					final int unreachableTransitionsResult = computeNumberOfUnreachableTransitions(mResult, mServices);
					if (unreachableTransitionsResult != 0) {
						correct = false;
						throw new AssertionError("removed transitions: " + unreachableTransitionsResult + "result has "
								+ mResult.getTransitions().size());
					}
				}
			}
			if (mDsi.isVitalityPreserved()) {
				final int deadTransitionsMinuend = computeNumberOfDeadTransitions(mMinuend, mServices);
				if (deadTransitionsMinuend == 0) {
					final int deadTransitionsResult = computeNumberOfDeadTransitions(mResult, mServices);
					if (deadTransitionsResult != 0) {
						correct = false;
						throw new AssertionError("removed transitions: " + deadTransitionsResult + "result has "
								+ mResult.getTransitions().size());
					}
				}
			}
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		return correct;
	}

	private static <LETTER, PLACE> int computeNumberOfDeadTransitions(final IPetriNet<LETTER, PLACE> result,
			final AutomataLibraryServices services)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final int transitionsBefore = (result.getTransitions()).size();
		final BoundedPetriNet<LETTER, PLACE> removeDead = new RemoveDead<>(services, result).getResult();
		final int transitionsAfterwards = (removeDead.getTransitions().size());
		final int transitionsRemovedByMinimization = transitionsBefore - transitionsAfterwards;
		return transitionsRemovedByMinimization;
	}

	private static <LETTER, PLACE> int computeNumberOfUnreachableTransitions(final IPetriNet<LETTER, PLACE> result,
			final AutomataLibraryServices services)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final int transitionsBefore = (result.getTransitions()).size();
		final IPetriNet<LETTER, PLACE> removeUnreachableResult = new RemoveUnreachable<>(services, result).getResult();
		final int transitionsAfterwards = (removeUnreachableResult.getTransitions().size());
		final int transitionsRemovedByMinimization = transitionsBefore - transitionsAfterwards;
		return transitionsRemovedByMinimization;
	}

	private static <E> E onlyElement(final Iterable<E> iterable) {
		final Iterator<E> iter = iterable.iterator();
		assert iter.hasNext() : "Expected one element, found none.";
		final E result = iter.next();
		assert !iter.hasNext() : "Expected one element, found more.";
		return result;
	}

	private static <E> E atMostOneElement(final Iterable<E> iterable) {
		final Iterator<E> iter = iterable.iterator();
		if (!iter.hasNext()) {
			return null;
		}
		final E result = iter.next();
		if (iter.hasNext()) {
			throw new AssertionError("Expected at most one element, found more, probably the second arguement"
					+ " of the difference operation is not deterministic.");
		}
		return result;
	}

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		int looperOnlyLetters = 0;
		int moreChangersThanLoopers = 0;
		for (final Transition<LETTER, PLACE> oldTrans : mMinuend.getTransitions()) {
			final Set<PLACE> loopers = mDsi.getSelfloops().getImage(oldTrans);
			final Set<PLACE> changers = mDsi.getStateChangers().getImage(oldTrans);
			if (changers == null || changers.isEmpty()) {
				++looperOnlyLetters;
			}
			if (changers != null && changers.size() > loopers.size()) {
				++moreChangersThanLoopers;
			}
		}
		final AutomataOperationStatistics statistics = new AutomataOperationStatistics();
		statistics.addKeyValuePair(StatisticsType.PETRI_ALPHABET, mResult.getAlphabet().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_PLACES, mResult.getPlaces().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_TRANSITIONS, mResult.getTransitions().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_FLOW, mResult.flowSize());
		statistics.addKeyValuePair(StatisticsType.PETRI_DIFFERENCE_MINUEND_PLACES, mMinuend.getPlaces().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_DIFFERENCE_MINUEND_TRANSITIONS,
				mMinuend.getTransitions().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_DIFFERENCE_MINUEND_FLOW, mMinuend.flowSize());
		statistics.addKeyValuePair(StatisticsType.PETRI_DIFFERENCE_SUBTRAHEND_STATES, mSubtrahend.getStates().size());
		statistics.addKeyValuePair(StatisticsType.PETRI_DIFFERENCE_SUBTRAHEND_LOOPER_ONLY_LETTERS, looperOnlyLetters);
		statistics.addKeyValuePair(StatisticsType.PETRI_DIFFERENCE_SUBTRAHEND_LETTERS_WITH_MORE_CHANGERS_THAN_LOOPERS,
				moreChangersThanLoopers);
		return statistics;
	}

}
