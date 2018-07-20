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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
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
 *            Type of letters from the alphabet
 * @param <C>
 *            content type
 * @param <CRSF>
 *            check result state factory type
 */
public final class DifferenceBlackAndWhite
		<LETTER, C, CRSF extends IPetriNet2FiniteAutomatonStateFactory<C> & INwaInclusionStateFactory<C>>
		extends UnaryNetOperation<LETTER, C, CRSF> {

	private final BoundedPetriNet<LETTER, C> mOperand;
	private final INestedWordAutomaton<LETTER, C> mNwa;
	private final IBlackWhiteStateFactory<C> mContentFactory;

	private BoundedPetriNet<LETTER, C> mResult;

	private final Map<Place<C>, Place<C>> mOldPlace2NewPlace = new HashMap<>();

	private final Map<LETTER, Set<C>> mSelfloop = new HashMap<>();
	private final Map<LETTER, Set<C>> mStateChanger = new HashMap<>();

	private final Map<C, Place<C>> mWhitePlace = new HashMap<>();
	private final Map<C, Place<C>> mBlackPlace = new HashMap<>();

	public <SF extends IBlackWhiteStateFactory<C> & ISinkStateFactory<C>> DifferenceBlackAndWhite(
			final AutomataLibraryServices services, final SF factory, final BoundedPetriNet<LETTER, C> net,
			final INestedWordAutomaton<LETTER, C> nwa) {
		super(services);
		mOperand = net;
		mNwa = nwa;
		mContentFactory = factory;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		assert checkMostSubtrahendProperties();
		if (nwa.isFinal(onlyElement(nwa.getInitialStates()))) {
			// subtrahend accepts everything (because of its special properties)
			// --> difference is empty
			mResult = new BoundedPetriNet<>(mServices, mOperand.getAlphabet(), mOperand.getStateFactory(), true);
			final C sinkContent = factory.createSinkStateContent();
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
		if (!NestedWordAutomataUtils.isFiniteAutomaton(mNwa)) {
			throw new IllegalArgumentException("subtrahend must be a finite automaton");
		} else if (!IAutomaton.sameAlphabet(mOperand, mNwa)) {
			// not really necessary, but different alphabets could be hinting at bugs in other operations
			throw new IllegalArgumentException("minuend and subtrahend must use same alphabet");
		} else if (mNwa.getInitialStates().size() != 1) {
			throw new IllegalArgumentException("subtrahend must have exactly one inital state");
		} else if (!finalStatesAreTraps()) {
			throw new IllegalArgumentException("subtrahend's final states must be trap states");
		}
		return true;
	}
	
	private boolean finalStatesAreTraps() {
		for (final C finalState : mNwa.getFinalStates()) {
			if (!stateIsTrap(finalState)) {
				return false;
			}
		}
		return true;
	}
	
	private boolean stateIsTrap(final C state) {
		for (final LETTER letter : mNwa.getVpAlphabet().getInternalAlphabet()) {
			boolean noSuccessors = true;
			for (final OutgoingInternalTransition<LETTER, C> out : mNwa.internalSuccessors(state, letter)) {
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
		return "Start " + getOperationName() + "First Operand " + mOperand.sizeInformation() + "Second Operand "
				+ mNwa.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mResult.sizeInformation();
	}

	private void partitionStates() {
		for (final LETTER symbol : mNwa.getVpAlphabet().getInternalAlphabet()) {
			final Set<C> selfloopStates = new HashSet<>();
			final Set<C> changerStates = new HashSet<>();
			for (final C state : mNwa.getStates()) {
				if (mNwa.isFinal(state)) {
					// final states are not copied to the result because of subtrahend's special properties
					continue;
				}
				final OutgoingInternalTransition<LETTER, C> successors = atMostOneElement(mNwa.internalSuccessors(state, symbol));
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
		// the correct "constantTokenAmmount" could be computed after "addBlackAndWhitePlaces()" using
		// mOperand.constantTokenAmount() && mBlackPlace.size() == mWhitePlace.size()
		final boolean constantTokenAmount = false;
		mResult = new BoundedPetriNet<>(mServices, mOperand.getAlphabet(), mOperand.getStateFactory(), constantTokenAmount);

		for (final Place<C> oldPlace : mOperand.getPlaces()) {
			final C content = oldPlace.getContent();
			final boolean isInitial = mOperand.getInitialMarking().contains(oldPlace);
			final boolean isAccepting = mOperand.getAcceptingPlaces().contains(oldPlace);
			final Place<C> newPlace = mResult.addPlace(content, isInitial, isAccepting);
			mOldPlace2NewPlace.put(oldPlace, newPlace);
		}
	}
	
	/**
	 * Heuristic for choosing a synchronization method for all transitions with a given letter.
	 * @param symbol Label of transitions to be synchronized.
	 * @return Use {@link #syncWithAnySelfloop(ITransition)}, else use {@link #syncWithEachSelfloop(ITransition)}
	 */
	private boolean invertSyncWithSelfloops(final LETTER symbol) {
		return mSelfloop.get(symbol).size() >= mStateChanger.get(symbol).size();
	}
	
	private Set<C> requiredBlackPlaces() {
		Set<C> requiredBlack = new HashSet<>();
		for (LETTER symbol : mOperand.getAlphabet()) {
			if (invertSyncWithSelfloops(symbol)) {
				requiredBlack.addAll(mStateChanger.get(symbol));
			}
		}
		return requiredBlack;
	}
	
	private void addBlackAndWhitePlaces() {
		for (final C state : mNwa.getStates()) {
			if (mNwa.isFinal(state)) {
				continue;
			}
			final boolean isInitial = mNwa.getInitialStates().contains(state);
			final C whiteContent = mContentFactory.getWhiteContent(state);
			final Place<C> whitePlace = mResult.addPlace(whiteContent, isInitial, false);
			mWhitePlace.put(state, whitePlace);
		}
		for (final C state : requiredBlackPlaces()) {
			final boolean isInitial = mNwa.getInitialStates().contains(state);
			final C blackContent = mContentFactory.getBlackContent(state);
			final Place<C> blackPlace = mResult.addPlace(blackContent, !isInitial, false);
			mBlackPlace.put(state, blackPlace);
		}
	}

	private void addTransitions() {
		for (final ITransition<LETTER, C> oldTrans : mOperand.getTransitions()) {
			final LETTER symbol = oldTrans.getSymbol();
			for (final C predState : mStateChanger.get(symbol)) {
				syncWithChanger(oldTrans, predState);
			}
			syncWithSelfloops(oldTrans);
		}
	}
	
	private void syncWithChanger(final ITransition<LETTER, C> oldTrans,  final C predState) {
		final C succState = onlyElement(mNwa.internalSuccessors(predState, oldTrans.getSymbol())).getSucc();
		if (mNwa.isFinal(succState)) {
			// optimization for special structure of subtrahend automata
			return;
		}
		final Collection<Place<C>> predecessors = new ArrayList<>();
		final Collection<Place<C>> successors = new ArrayList<>();
		predecessors.add(mWhitePlace.get(predState));
		successors.add(mWhitePlace.get(succState));
		final Place<C> blackSucc = mBlackPlace.get(succState);
		final Place<C> blackPred = mBlackPlace.get(predState);
		if (blackSucc != null) {
			predecessors.add(blackSucc);
		}
		if (blackPred != null) {
			successors.add(blackPred);
		}
		copyMinuendFlow(oldTrans, predecessors, successors);
		mResult.addTransition(oldTrans.getSymbol(), predecessors, successors);
	}

	private void syncWithSelfloops(final ITransition<LETTER, C> oldTrans) {
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
	private void syncWithEachSelfloop(final ITransition<LETTER, C> oldTrans) {
		// Relies on the special properties of the subtrahend, usually we would have to sync at least
		// with the selfloop of the implicit (!) sink state which is not in mSelfloop.get(symbol)
		final LETTER symbol = oldTrans.getSymbol();
		for (final C state : mSelfloop.get(symbol)) {
			final Collection<Place<C>> predecessors = new ArrayList<>();
			final Collection<Place<C>> successors = new ArrayList<>();
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
	private void syncWithAnySelfloop(final ITransition<LETTER, C> oldTrans) {
		final LETTER symbol = oldTrans.getSymbol();
		if (mSelfloop.get(symbol).isEmpty()) {
			// This optimization relies on the special properties of the subtrahend.
			// Usually we would have to sync at least with the selfloop of the implicit (!) sink state.
			return;
		}
		final Collection<Place<C>> predecessors = new ArrayList<>();
		final Collection<Place<C>> successors = new ArrayList<>();
		copyMinuendFlow(oldTrans, predecessors, successors);
		for (final C state : mStateChanger.get(symbol)) {
			predecessors.add(mBlackPlace.get(state));
			successors.add(mBlackPlace.get(state));
		}
		mResult.addTransition(symbol, predecessors, successors);
	}

	private void copyMinuendFlow(final ITransition<LETTER, C> trans,
			final Collection<Place<C>> preds, final Collection<Place<C>> succs) {
		for (final Place<C> oldPlace : trans.getPredecessors()) {
			preds.add(mOldPlace2NewPlace.get(oldPlace));
		}
		for (final Place<C> oldPlace : trans.getSuccessors()) {
			succs.add(mOldPlace2NewPlace.get(oldPlace));
		}
	}
	
	@Override
	protected IPetriNet<LETTER, C> getOperand() {
		return mOperand;
	}

	@Override
	public BoundedPetriNet<LETTER, C> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Testing correctness of " + getOperationName());
		}

		final INestedWordAutomaton<LETTER, C> op1AsNwa =
				(new PetriNet2FiniteAutomaton<>(mServices, stateFactory, mOperand)).getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, C> rcResult =
				(new DifferenceDD<>(mServices, stateFactory, op1AsNwa, mNwa)).getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, C> resultAsNwa =
				(new PetriNet2FiniteAutomaton<>(mServices, stateFactory, mResult)).getResult();

		boolean correct = true;
		correct &= new IsEquivalent<>(mServices, stateFactory, resultAsNwa, rcResult).getResult();

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		return correct;
	}
	
	private static <E> E onlyElement(final Iterable<E> iterable) {
		Iterator<E> iter = iterable.iterator();
		assert iter.hasNext() : "Expected one element, found none.";
		final E result = iter.next();
		assert !iter.hasNext() : "Expected one element, found more.";
		return result;
	}
	
	private static <E> E atMostOneElement(final Iterable<E> iterable) {
		Iterator<E> iter = iterable.iterator();
		if (!iter.hasNext()) {
			return null;
		}
		final E result = iter.next();
		assert !iter.hasNext() : "Expected one element, found more.";
		return result;
	}
}
