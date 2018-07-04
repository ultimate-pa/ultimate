/*
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ConcurrentProduct;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IConcurrentProductStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <S>
 *            symbol type
 * @param <C>
 *            state/content type
 * @param <CRSF>
 *            check result state factory type
 */
public final class PrefixProduct<S, C, CRSF extends IPetriNet2FiniteAutomatonStateFactory<C> & IConcurrentProductStateFactory<C> & INwaInclusionStateFactory<C>>
		extends UnaryNetOperation<S, C, CRSF> {
	private final BoundedPetriNet<S, C> mOperand;
	private final INestedWordAutomaton<S, C> mNwa;
	private final BoundedPetriNet<S, C> mResult;

	private final Map<Place<S, C>, Place<S, C>> mOldPlace2newPlace = new HashMap<>();
	private final Map<C, Place<S, C>> mState2newPlace = new HashMap<>();

	private final Map<S, Collection<ITransition<S, C>>> mSymbol2netTransitions = new HashMap<>();
	private final Map<S, Collection<AutomatonTransition>> mSymbol2nwaTransitions = new HashMap<>();

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @param nwa
	 *            nested word automaton
	 */
	public PrefixProduct(final AutomataLibraryServices services, final BoundedPetriNet<S, C> operand,
			final INestedWordAutomaton<S, C> nwa) {
		super(services);
		mOperand = operand;
		mNwa = nwa;
		if (nwa.getInitialStates().size() != 1) {
			throw new UnsupportedOperationException("PrefixProduct needs an automaton with exactly one inital state");
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mResult = computeResult();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String startMessage() {
		return "Start " + getOperationName() + "First Operand " + mOperand.sizeInformation() + "Second Operand "
				+ mNwa.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " Result " + mResult.sizeInformation();
	}

	@Override
	protected IPetriNet<S, C> getOperand() {
		return mOperand;
	}

	@Override
	public BoundedPetriNet<S, C> getResult() {
		return mResult;
	}

	private void updateSymbol2netTransitions(final S symbol, final ITransition<S, C> netTransition) {
		Collection<ITransition<S, C>> netTransitions;
		netTransitions = mSymbol2netTransitions.get(symbol);
		if (netTransitions == null) {
			netTransitions = new LinkedList<>();
			mSymbol2netTransitions.put(symbol, netTransitions);
		}
		netTransitions.add(netTransition);
	}

	private void updateSymbol2nwaTransitions(final S symbol, final AutomatonTransition nwaTransition) {
		Collection<AutomatonTransition> nwaTransitions;
		nwaTransitions = mSymbol2nwaTransitions.get(symbol);
		if (nwaTransitions == null) {
			nwaTransitions = new LinkedList<>();
			mSymbol2nwaTransitions.put(symbol, nwaTransitions);
		}
		nwaTransitions.add(nwaTransition);
	}

	private BoundedPetriNet<S, C> computeResult() {
		final HashSet<S> netOnlyAlphabet = new HashSet<>(mOperand.getAlphabet());
		netOnlyAlphabet.removeAll(mNwa.getVpAlphabet().getInternalAlphabet());
		final HashSet<S> sharedAlphabet = new HashSet<>(mOperand.getAlphabet());
		sharedAlphabet.removeAll(netOnlyAlphabet);
		final HashSet<S> nwaOnlyAlphabet = new HashSet<>(mNwa.getVpAlphabet().getInternalAlphabet());
		nwaOnlyAlphabet.removeAll(sharedAlphabet);
		final HashSet<S> unionAlphabet = new HashSet<>(mOperand.getAlphabet());
		unionAlphabet.addAll(nwaOnlyAlphabet);

		// prefix product preserves the constantTokenAmount invariant
		final boolean constantTokenAmount = mOperand.constantTokenAmount();
		final BoundedPetriNet<S, C> result =
				new BoundedPetriNet<>(mServices, unionAlphabet, mOperand.getStateFactory(), constantTokenAmount);

		addPlacesAndStates();

		for (final ITransition<S, C> trans : mOperand.getTransitions()) {
			updateSymbol2netTransitions(trans.getSymbol(), trans);
		}

		for (final C state : mNwa.getStates()) {
			for (final OutgoingInternalTransition<S, C> trans : mNwa.internalSuccessors(state)) {
				final S letter = trans.getLetter();
				final C succ = trans.getSucc();
				Collection<AutomatonTransition> automatonTransitions = mSymbol2nwaTransitions.get(letter);
				if (automatonTransitions == null) {
					automatonTransitions = new HashSet<>();
					mSymbol2nwaTransitions.put(letter, automatonTransitions);
				}
				automatonTransitions.add(new AutomatonTransition(state, letter, succ));
			}
		}

		addUnsharedTransitions(netOnlyAlphabet, nwaOnlyAlphabet);

		addSharedTransitions(sharedAlphabet);
		return result;
	}

	private void addSharedTransitions(final HashSet<S> sharedAlphabet) {
		for (final S symbol : sharedAlphabet) {
			if (!mSymbol2netTransitions.containsKey(symbol)) {
				continue;
			}
			for (final ITransition<S, C> netTrans : mSymbol2netTransitions.get(symbol)) {
				if (!mSymbol2nwaTransitions.containsKey(symbol)) {
					continue;
				}
				for (final AutomatonTransition nwaTrans : mSymbol2nwaTransitions.get(symbol)) {
					final Collection<Place<S, C>> predecessors = new ArrayList<>();
					addSharedTransitionsHelper(netTrans, nwaTrans, predecessors);
				}
			}
		}
	}

	private void addUnsharedTransitions(final HashSet<S> netOnlyAlphabet, final HashSet<S> nwaOnlyAlphabet) {
		for (final S symbol : netOnlyAlphabet) {
			for (final ITransition<S, C> trans : mSymbol2netTransitions.get(symbol)) {
				final Collection<Place<S, C>> predecessors = new ArrayList<>();
				for (final Place<S, C> oldPlace : trans.getPredecessors()) {
					final Place<S, C> newPlace = mOldPlace2newPlace.get(oldPlace);
					predecessors.add(newPlace);
				}
				final Collection<Place<S, C>> successors = new ArrayList<>();
				for (final Place<S, C> oldPlace : trans.getSuccessors()) {
					final Place<S, C> newPlace = mOldPlace2newPlace.get(oldPlace);
					successors.add(newPlace);
				}
				mResult.addTransition(trans.getSymbol(), predecessors, successors);
			}
		}

		for (final S symbol : nwaOnlyAlphabet) {
			for (final AutomatonTransition trans : mSymbol2nwaTransitions.get(symbol)) {
				final Collection<Place<S, C>> predecessors = new ArrayList<>(1);
				final Place<S, C> newPlacePred = mState2newPlace.get(trans.getPredecessor());
				predecessors.add(newPlacePred);

				final Collection<Place<S, C>> successors = new ArrayList<>(1);
				final Place<S, C> newPlaceSucc = mState2newPlace.get(trans.getSuccessor());
				successors.add(newPlaceSucc);
				mResult.addTransition(trans.getSymbol(), predecessors, successors);
			}
		}
	}

	private void addSharedTransitionsHelper(final ITransition<S, C> netTrans, final AutomatonTransition nwaTrans,
			final Collection<Place<S, C>> predecessors) {
		for (final Place<S, C> oldPlace : netTrans.getPredecessors()) {
			final Place<S, C> newPlace = mOldPlace2newPlace.get(oldPlace);
			predecessors.add(newPlace);
		}
		predecessors.add(mState2newPlace.get(nwaTrans.getPredecessor()));

		final Collection<Place<S, C>> successors = new ArrayList<>();
		for (final Place<S, C> oldPlace : netTrans.getSuccessors()) {
			final Place<S, C> newPlace = mOldPlace2newPlace.get(oldPlace);
			successors.add(newPlace);
		}
		successors.add(mState2newPlace.get(nwaTrans.getSuccessor()));
		mResult.addTransition(netTrans.getSymbol(), predecessors, successors);
	}

	private void addPlacesAndStates() {
		//add places of old net
		for (final Place<S, C> oldPlace : mOperand.getPlaces()) {
			final C content = oldPlace.getContent();
			final boolean isInitial = mOperand.getInitialMarking().contains(oldPlace);
			final boolean isAccepting = mOperand.getAcceptingPlaces().contains(oldPlace);
			final Place<S, C> newPlace = mResult.addPlace(content, isInitial, isAccepting);
			mOldPlace2newPlace.put(oldPlace, newPlace);
		}

		//add states of automaton
		for (final C state : mNwa.getStates()) {
			final C content = state;
			final boolean isInitial = mNwa.getInitialStates().contains(state);
			final boolean isAccepting = mNwa.isFinal(state);
			final Place<S, C> newPlace = mResult.addPlace(content, isInitial, isAccepting);
			mState2newPlace.put(state, newPlace);
		}
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataLibraryException {
		mLogger.info("Testing correctness of prefixProduct");

		final INwaOutgoingLetterAndTransitionProvider<S, C> op1AsNwa =
				(new PetriNet2FiniteAutomaton<>(mServices, stateFactory, mOperand)).getResult();
		final INwaOutgoingLetterAndTransitionProvider<S, C> resultAsNwa =
				(new PetriNet2FiniteAutomaton<>(mServices, stateFactory, mResult)).getResult();
		final INwaOutgoingLetterAndTransitionProvider<S, C> nwaResult =
				(new ConcurrentProduct<>(mServices, stateFactory, op1AsNwa, mNwa, true)).getResult();
		boolean correct;
		correct = (new IsEquivalent<>(mServices, stateFactory, resultAsNwa, nwaResult)).getResult();

		mLogger.info("Finished testing correctness of prefixProduct");
		return correct;
	}

	/**
	 * A transition of the result.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class AutomatonTransition {
		private final C mPredecessor;
		private final S mLetter;
		private final C mSuccessor;

		public AutomatonTransition(final C predecessor, final S letter, final C successor) {
			mPredecessor = predecessor;
			mLetter = letter;
			mSuccessor = successor;
		}

		public C getPredecessor() {
			return mPredecessor;
		}

		public S getSymbol() {
			return mLetter;
		}

		public C getSuccessor() {
			return mSuccessor;
		}
	}
}
