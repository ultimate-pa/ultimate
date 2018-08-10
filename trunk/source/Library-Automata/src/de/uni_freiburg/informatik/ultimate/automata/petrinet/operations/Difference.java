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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;

/**
 * Computes the difference between a {@link BoundedPetriNet} and an {@link INestedWordAutomaton}.
 * This operation is specialized for subtrahend automata with the following properties.
 * Results for other subtrahend automata may or may not be correct.
 * <p>
 * Properties of the subtrahend automata:
 * <ul>
 *   <li>Subtrahend is a deterministic finite automaton (DFA).
 *   <li>Transitions to a sink state are optional,
 *       but for every reachable a-transition in the minuend petri net,
 *       there is an explicit a-transition on every state in the subtrahend automaton.
 *   <li>Once a final state is reached it cannot be left,
 *       that is final states have a selfloop for each letter from the alphabet.
 * <ul>
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
public final class Difference
		<LETTER, PLACE, CRSF extends IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
		extends GeneralOperation<LETTER, PLACE, CRSF> {

	/**
	 * Synchronization with self-loops in subtrahend DFA can be done
	 * using different methods. In theory, the synchronization method can be chosen per self-loop.
	 * The synchronization methods listed here are used for all self-loops.
	 * However, some of the synchronization methods may decide per self-loop how to synchronize.
	 */
	public enum LoopSyncMethod {
		/**
		 * Synchronize with each LETTER-self-loop in subtrahend DFA
		 * by inserting a transition for each LETTER-transition in the minuend Petri net.
		 */
		PAIRWISE,
		/**
		 * Synchronize with all LETTER-self-loops in subtrahend DFA
		 * by inserting a single transition for all LETTER-transition in the minuend Petri net together.
		 * The new transition checks that the subtrahend DFA is not in a LETTER-changer state
		 * (a state that can be left by reading LETTER) by checking black places of said changer states.
		 */
		INVERTED,
		/**
		 * For each LETTER decide whether to use {@link #PAIRWISE} or {@link #INVERTED}
		 * trying to minimize the resulting difference Petri net using a heuristic.
		 */
		HEURISTIC,
	}
	
	private final LoopSyncMethod mLoopSyncMethod;
	
	private final BoundedPetriNet<LETTER, PLACE> mMinuend;
	private final INestedWordAutomaton<LETTER, PLACE> mSubtrahend;
	private final IBlackWhiteStateFactory<PLACE> mContentFactory;

	private BoundedPetriNet<LETTER, PLACE> mResult;

	private final Map<PLACE, PLACE> mOldPlace2NewPlace = new HashMap<>();

	private final Map<LETTER, Set<PLACE>> mSelfloop = new HashMap<>();
	private final Map<LETTER, Set<PLACE>> mStateChanger = new HashMap<>();

	private final Map<PLACE, PLACE> mWhitePlace = new HashMap<>();
	private final Map<PLACE, PLACE> mBlackPlace = new HashMap<>();

	public <SF extends IBlackWhiteStateFactory<PLACE> & ISinkStateFactory<PLACE>> Difference(
			final AutomataLibraryServices services, final SF factory,
			final BoundedPetriNet<LETTER, PLACE> minuendNet,
			final INestedWordAutomaton<LETTER, PLACE> subtrahendDfa) {
		this(services, factory, minuendNet, subtrahendDfa, LoopSyncMethod.HEURISTIC);
	}

	public <SF extends IBlackWhiteStateFactory<PLACE> & ISinkStateFactory<PLACE>> Difference(
			final AutomataLibraryServices services, final SF factory,
			final BoundedPetriNet<LETTER, PLACE> minuendNet,
			final INestedWordAutomaton<LETTER, PLACE> subtrahendDfa,
			final String loopSyncMethod) {
		this(services, factory, minuendNet, subtrahendDfa, LoopSyncMethod.valueOf(loopSyncMethod));
	}

	public <SF extends IBlackWhiteStateFactory<PLACE> & ISinkStateFactory<PLACE>> Difference(
			final AutomataLibraryServices services, final SF factory,
			final BoundedPetriNet<LETTER, PLACE> minuendNet,
			final INestedWordAutomaton<LETTER, PLACE> subtrahendDfa,
			final LoopSyncMethod loopSyncMethod) {
		super(services);
		mMinuend = minuendNet;
		mSubtrahend = subtrahendDfa;
		mContentFactory = factory;
		mLoopSyncMethod = loopSyncMethod;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		assert checkMostSubtrahendProperties();
		if (subtrahendDfa.isFinal(onlyElement(subtrahendDfa.getInitialStates()))) {
			// subtrahend accepts everything (because of its special properties)
			// --> difference is empty
			mResult = new BoundedPetriNet<>(mServices, mMinuend.getAlphabet(), true);
			final PLACE sinkContent = factory.createSinkStateContent();
			mResult.addPlace(sinkContent, true, false);
		} else {
			partitionStates();
			copyNetPlaces();
			addBlackAndWhitePlaces();
			addTransitions();
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	private boolean checkMostSubtrahendProperties() {
		// omitted check: Reachable transitions from minuend have sync partners in subtrahend
		if (!NestedWordAutomataUtils.isFiniteAutomaton(mSubtrahend)) {
			throw new IllegalArgumentException("subtrahend must be a finite automaton");
		} else if (!IAutomaton.sameAlphabet(mMinuend, mSubtrahend)) {
			// not really necessary, but different alphabets could be hinting at bugs in other operations
			throw new IllegalArgumentException("minuend and subtrahend must use same alphabet");
		} else if (mSubtrahend.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("subtrahend must have exactly one inital state");
			// TODO 2018-08-10 Matthias: I commented the following two lines because we
			// somehow what to tolerate subtrahends whose language is not necessarily closed
			// under concatenation with sigma^*. E.g., if we construct the subtrahend
			// on-demand with the assumption that the final state is a trap, we will not
			// get outgoing transitions from the accepting state because they will not
			// contribute to the result of the difference.
			// The cleanest solution might be that we specify the resulting language
			// of this operation not as L(N)-L(A) but as L(N)-(L(A)◦∑).
//		} else if (!finalStatesAreTraps()) {
//			throw new IllegalArgumentException("subtrahend's final states must be trap states");
		}
		return true;
	}

	private boolean finalStatesAreTraps() {
		for (final PLACE finalState : mSubtrahend.getFinalStates()) {
			if (!stateIsTrap(finalState)) {
				return false;
			}
		}
		return true;
	}

	private boolean stateIsTrap(final PLACE state) {
		for (final LETTER letter : mSubtrahend.getVpAlphabet().getInternalAlphabet()) {
			boolean noSuccessors = true;
			for (final OutgoingInternalTransition<LETTER, PLACE> out : mSubtrahend.internalSuccessors(state, letter)) {
				if (!out.getSucc().equals(state)) {
					return false;
				}
				noSuccessors = false;
			}
			if (noSuccessors) {
				return false;
			}
		}
		return true;
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName() + "First Operand " + mMinuend.sizeInformation() + "Second Operand "
				+ mSubtrahend.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mResult.sizeInformation();
	}

	private void partitionStates() {
		for (final LETTER symbol : mSubtrahend.getVpAlphabet().getInternalAlphabet()) {
			final Set<PLACE> selfloopStates = new HashSet<>();
			final Set<PLACE> changerStates = new HashSet<>();
			for (final PLACE state : mSubtrahend.getStates()) {
				if (mSubtrahend.isFinal(state)) {
					// final states are not copied to the result because of subtrahend's special properties
					continue;
				}
				final OutgoingInternalTransition<LETTER, PLACE> successors =
						atMostOneElement(mSubtrahend.internalSuccessors(state, symbol));
				if (successors == null) {
					continue;
				} else if (successors.getSucc().equals(state)) {
					selfloopStates.add(state);
				} else {
					changerStates.add(state);
				}
			}
			mSelfloop.put(symbol, selfloopStates);
			mStateChanger.put(symbol, changerStates);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(symbol + " has " + selfloopStates.size() + " selfloop and "
						+ changerStates.size() + " changer(s)");
			}
		}
	}

	private void copyNetPlaces() {
		// the correct "constantTokenAmmount" could be computed after "addBlackAndWhitePlaces()" using ...
		//   mOperand.constantTokenAmount() && mBlackPlace.size() == mWhitePlace.size()
		// ... but field has to be set in constructor and cannot be changed afterwards.
		final boolean constantTokenAmount = false;
		mResult = new BoundedPetriNet<>(mServices, mMinuend.getAlphabet(), constantTokenAmount);

		for (final PLACE oldPlace : mMinuend.getPlaces()) {
			final PLACE content = oldPlace;
			final boolean isInitial = mMinuend.getInitialPlaces().contains(oldPlace);
			final boolean isAccepting = mMinuend.getAcceptingPlaces().contains(oldPlace);
			final PLACE newPlace = mResult.addPlace(content, isInitial, isAccepting);
			mOldPlace2NewPlace.put(oldPlace, newPlace);
		}
	}

	/**
	 * Heuristic for choosing a synchronization method for all transitions with a given letter.
	 * @param symbol Label of transitions to be synchronized.
	 * @return Use {@link #syncWithAnySelfloop(ITransition)}, else use {@link #syncWithEachSelfloop(ITransition)}
	 */
	private boolean invertSyncWithSelfloops(final LETTER symbol) {
		return mLoopSyncMethod == LoopSyncMethod.INVERTED || (mLoopSyncMethod == LoopSyncMethod.HEURISTIC
				&& mSelfloop.get(symbol).size() >= mStateChanger.get(symbol).size());
	}

	private Set<PLACE> requiredBlackPlaces() {
		final Set<PLACE> requiredBlack = new HashSet<>();
		for (final LETTER symbol : mMinuend.getAlphabet()) {
			if (invertSyncWithSelfloops(symbol)) {
				requiredBlack.addAll(mStateChanger.get(symbol));
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
			final PLACE whiteContent = mContentFactory.getWhiteContent(state);
			final PLACE whitePlace = mResult.addPlace(whiteContent, isInitial, false);
			mWhitePlace.put(state, whitePlace);
		}
		for (final PLACE state : requiredBlackPlaces()) {
			final boolean isInitial = mSubtrahend.getInitialStates().contains(state);
			final PLACE blackContent = mContentFactory.getBlackContent(state);
			final PLACE blackPlace = mResult.addPlace(blackContent, !isInitial, false);
			mBlackPlace.put(state, blackPlace);
		}
	}

	private void addTransitions() {
		for (final ITransition<LETTER, PLACE> oldTrans : mMinuend.getTransitions()) {
			final LETTER symbol = oldTrans.getSymbol();
			for (final PLACE predState : mStateChanger.get(symbol)) {
				syncWithChanger(oldTrans, predState);
			}
			syncWithSelfloops(oldTrans);
		}
	}

	private void syncWithChanger(final ITransition<LETTER, PLACE> oldTrans,  final PLACE predState) {
		final PLACE succState = onlyElement(mSubtrahend.internalSuccessors(predState, oldTrans.getSymbol())).getSucc();
		if (mSubtrahend.isFinal(succState)) {
			// optimization for special structure of subtrahend automata:
			// omit this transition because subtrahend will accept everything afterwards
			return;
		}
		final Set<PLACE> predecessors = new HashSet<>();
		final Set<PLACE> successors = new HashSet<>();
		predecessors.add(mWhitePlace.get(predState));
		successors.add(mWhitePlace.get(succState));
		final PLACE blackSucc = mBlackPlace.get(succState);
		final PLACE blackPred = mBlackPlace.get(predState);
		if (blackSucc != null) {
			predecessors.add(blackSucc);
		}
		if (blackPred != null) {
			successors.add(blackPred);
		}
		copyMinuendFlow(oldTrans, predecessors, successors);
		mResult.addTransition(oldTrans.getSymbol(), predecessors, successors);
	}

	private void syncWithSelfloops(final ITransition<LETTER, PLACE> oldTrans) {
		if (invertSyncWithSelfloops(oldTrans.getSymbol())) {
			syncWithAnySelfloop(oldTrans);
		} else {
			syncWithEachSelfloop(oldTrans);
		}
	}

	/**
	 * Synchronizes a transition from the minuend Petri net with all related transitions of the subtrahend automaton.
	 * Synchronization is done the same way as synchronization with changers. For every transition in the
	 * subtrahend automaton a transition is inserted in the result.
	 * <p>
	 * Pros:
	 * <ul>
	 *   <li> No black places needed
	 *   <li> Inserted transitions have low degree
	 * </ul>
	 * Cons:
	 * <ul>
	 *   <li> Inserts multiple transitions, one per sync partner
	 * </ul>
	 * This approach is optimized for cases in which the subtrahend automaton has only few selfloops
	 * (with the same symbol as the transition to be synchronized).
	 *
	 * @param oldTrans Minuend's transition to be synchronized with subtrahend
	 *
	 * @see #invertSyncWithSelfloops(LETTER)
	 */
	private void syncWithEachSelfloop(final ITransition<LETTER, PLACE> oldTrans) {
		// Relies on the special properties of the subtrahend, usually we would have to sync at least
		// with the selfloop of the implicit (!) sink state which is not in mSelfloop.get(symbol)
		final LETTER symbol = oldTrans.getSymbol();
		for (final PLACE state : mSelfloop.get(symbol)) {
			final Set<PLACE> predecessors = new HashSet<>();
			final Set<PLACE> successors = new HashSet<>();
			predecessors.add(mWhitePlace.get(state));
			successors.add(mWhitePlace.get(state));
			copyMinuendFlow(oldTrans, predecessors, successors);
			mResult.addTransition(oldTrans.getSymbol(), predecessors, successors);
		}
	}

	/**
	 * Synchronizes a transition from the minuend Petri net with all related transitions of the subtrahend automaton
	 * inserting just one new transition into the resulting difference Petri net.
	 * Instead of checking that the subtrahend automaton is in any selfloop state, checks that the subtrahen automaton
	 * is not in any other state.
	 * <p>
	 * Pros:
	 * <ul>
	 *   <li> One transition, no matter how many sync partners
	 * </ul>
	 * Cons:
	 * <ul>
	 *   <li> Needs Black places for every non-sync partner
	 *   <li> Inserted transition may have a very high degree
	 * </ul>
	 * This approach is optimized for cases in which the subtrahend automaton has a selfloop
	 * (with the same symbol as the transition to be synchronized) on nearly all of its states.
	 *
	 * @param oldTrans Minuend's transition to be synchronized with subtrahend
	 *
	 * @see #invertSyncWithSelfloops(LETTER)
	 */
	private void syncWithAnySelfloop(final ITransition<LETTER, PLACE> oldTrans) {
		final LETTER symbol = oldTrans.getSymbol();
		if (mSelfloop.get(symbol).isEmpty()) {
			// This optimization relies on the special properties of the subtrahend.
			// Usually we would have to sync at least with the selfloop of the implicit (!) sink state.
			return;
		}
		final Set<PLACE> predecessors = new HashSet<>();
		final Set<PLACE> successors = new HashSet<>();
		copyMinuendFlow(oldTrans, predecessors, successors);
		for (final PLACE state : mStateChanger.get(symbol)) {
			predecessors.add(mBlackPlace.get(state));
			successors.add(mBlackPlace.get(state));
		}
		mResult.addTransition(symbol, predecessors, successors);
	}

	private void copyMinuendFlow(final ITransition<LETTER, PLACE> trans,
			final Collection<PLACE> preds, final Collection<PLACE> succs) {
		for (final PLACE oldPlace : mMinuend.getPredecessors(trans)) {
			preds.add(mOldPlace2NewPlace.get(oldPlace));
		}
		for (final PLACE oldPlace : mMinuend.getSuccessors(trans)) {
			succs.add(mOldPlace2NewPlace.get(oldPlace));
		}
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

		final INestedWordAutomaton<LETTER, PLACE> op1AsNwa =
				(new PetriNet2FiniteAutomaton<>(mServices, stateFactory, mMinuend)).getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> rcResult =
				(new DifferenceDD<>(mServices, stateFactory, op1AsNwa, mSubtrahend)).getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> resultAsNwa =
				(new PetriNet2FiniteAutomaton<>(mServices, stateFactory, mResult)).getResult();

		boolean correct = true;
		correct &= new IsEquivalent<>(mServices, stateFactory, resultAsNwa, rcResult).getResult();

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		return correct;
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
		assert !iter.hasNext() : "Expected one element, found more.";
		return result;
	}

	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		int looperOnlyLetters = 0;
		int moreChangersThanLoopers = 0;
		for (final LETTER letter : mSubtrahend.getAlphabet()) {
			final Set<PLACE> loopers = mSelfloop.get(letter);
			final Set<PLACE> changers = mStateChanger.get(letter);
			if (changers == null || changers.isEmpty()) {
				++looperOnlyLetters;
			}
			if (changers != null && changers.size() > loopers.size()) {
				++moreChangersThanLoopers;
			}
		}
		final AutomataOperationStatistics statistics = new AutomataOperationStatistics();
		statistics.addKeyValuePair(
				StatisticsType.PETRI_ALPHABET, mResult.getAlphabet().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_PLACES , mResult.getPlaces().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_TRANSITIONS, mResult.getTransitions().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_FLOW, mResult.flowSize());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_DIFFERENCE_MINUEND_PLACES, mMinuend.getPlaces().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_DIFFERENCE_MINUEND_TRANSITIONS, mMinuend.getTransitions().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_DIFFERENCE_MINUEND_FLOW, mMinuend.flowSize());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_DIFFERENCE_SUBTRAHEND_STATES, mSubtrahend.getStates().size());
		statistics.addKeyValuePair(
				StatisticsType.PETRI_DIFFERENCE_SUBTRAHEND_LOOPER_ONLY_LETTERS, looperOnlyLetters);
		statistics.addKeyValuePair(
				StatisticsType.PETRI_DIFFERENCE_SUBTRAHEND_LETTERS_WITH_MORE_CHANGERS_THAN_LOOPERS,
				moreChangersThanLoopers);
		return statistics;
	}

}
