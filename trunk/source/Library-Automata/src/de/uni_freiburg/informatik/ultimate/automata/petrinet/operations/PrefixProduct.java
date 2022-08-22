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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ConcurrentProduct;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.PetriNetUtils;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IConcurrentProductStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Given a Petri net N and an finite automaton A over the same alphabet. The language of the {@link PrefixProduct} is
 * the set of all words w such that
 * <ul>
 * <li>w is the interleaving of two words w_N and w_A such that
 * <li>there is a run of N over w_N
 * <li>there is a run of A over w_A
 * <li>w_A is accepted by A or w_N is accepted by N </ ul>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <CRSF>
 *            check result state factory type
 */
public final class PrefixProduct<LETTER, PLACE, CRSF extends IPetriNet2FiniteAutomatonStateFactory<PLACE> & IConcurrentProductStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
		extends UnaryNetOperation<LETTER, PLACE, CRSF> {
	private final BoundedPetriNet<LETTER, PLACE> mOperand;
	private final INestedWordAutomaton<LETTER, PLACE> mNwa;
	private final BoundedPetriNet<LETTER, PLACE> mResult;

	private final Map<LETTER, Collection<Transition<LETTER, PLACE>>> mSymbol2netTransitions = new HashMap<>();
	private final Map<LETTER, Collection<AutomatonTransition>> mSymbol2nwaTransitions = new HashMap<>();

	public PrefixProduct(final AutomataLibraryServices services, final BoundedPetriNet<LETTER, PLACE> operand,
			final INestedWordAutomaton<LETTER, PLACE> nwa) {
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
	protected IPetriNet<LETTER, PLACE> getOperand() {
		return mOperand;
	}

	@Override
	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	private void updateSymbol2netTransitions(final LETTER symbol, final Transition<LETTER, PLACE> netTransition) {
		final Collection<Transition<LETTER, PLACE>> netTransitions =
				mSymbol2netTransitions.computeIfAbsent(symbol, x -> new LinkedList<>());
		netTransitions.add(netTransition);
	}

	private BoundedPetriNet<LETTER, PLACE> computeResult() {
		final HashSet<LETTER> netOnlyAlphabet = new HashSet<>(mOperand.getAlphabet());
		netOnlyAlphabet.removeAll(mNwa.getVpAlphabet().getInternalAlphabet());
		final HashSet<LETTER> sharedAlphabet = new HashSet<>(mOperand.getAlphabet());
		sharedAlphabet.removeAll(netOnlyAlphabet);
		final HashSet<LETTER> nwaOnlyAlphabet = new HashSet<>(mNwa.getVpAlphabet().getInternalAlphabet());
		nwaOnlyAlphabet.removeAll(sharedAlphabet);
		final HashSet<LETTER> unionAlphabet = new HashSet<>(mOperand.getAlphabet());
		unionAlphabet.addAll(nwaOnlyAlphabet);

		// prefix product preserves the constantTokenAmount invariant
		final boolean constantTokenAmount = mOperand.constantTokenAmount();
		final BoundedPetriNet<LETTER, PLACE> result =
				new BoundedPetriNet<>(mServices, unionAlphabet, constantTokenAmount);

		addPlacesAndStates(result);

		for (final Transition<LETTER, PLACE> trans : mOperand.getTransitions()) {
			updateSymbol2netTransitions(trans.getSymbol(), trans);
		}

		for (final PLACE state : mNwa.getStates()) {
			for (final OutgoingInternalTransition<LETTER, PLACE> trans : mNwa.internalSuccessors(state)) {
				final LETTER letter = trans.getLetter();
				final PLACE succ = trans.getSucc();
				final Collection<AutomatonTransition> automatonTransitions =
						mSymbol2nwaTransitions.computeIfAbsent(letter, x -> new HashSet<>());
				automatonTransitions.add(new AutomatonTransition(state, letter, succ));
			}
		}

		addUnsharedTransitions(netOnlyAlphabet, nwaOnlyAlphabet, result);

		addSharedTransitions(sharedAlphabet, result);
		return result;
	}

	private void addSharedTransitions(final HashSet<LETTER> sharedAlphabet,
			final BoundedPetriNet<LETTER, PLACE> result) {
		for (final LETTER symbol : sharedAlphabet) {
			if (!mSymbol2netTransitions.containsKey(symbol)) {
				continue;
			}
			for (final Transition<LETTER, PLACE> netTrans : mSymbol2netTransitions.get(symbol)) {
				if (!mSymbol2nwaTransitions.containsKey(symbol)) {
					continue;
				}
				for (final AutomatonTransition nwaTrans : mSymbol2nwaTransitions.get(symbol)) {
					final Set<PLACE> predecessors = new HashSet<>();
					addSharedTransitionsHelper(netTrans, nwaTrans, predecessors, result);
				}
			}
		}
	}

	private void addUnsharedTransitions(final HashSet<LETTER> netOnlyAlphabet, final HashSet<LETTER> nwaOnlyAlphabet,
			final BoundedPetriNet<LETTER, PLACE> result) {
		for (final LETTER symbol : netOnlyAlphabet) {
			for (final Transition<LETTER, PLACE> trans : mSymbol2netTransitions.get(symbol)) {
				result.addTransition(trans.getSymbol(), trans.getPredecessors(), trans.getSuccessors());
			}
		}

		for (final LETTER symbol : nwaOnlyAlphabet) {
			for (final AutomatonTransition trans : mSymbol2nwaTransitions.get(symbol)) {
				final Set<PLACE> predecessors = Set.of(trans.getPredecessor());
				final Set<PLACE> successors = Set.of(trans.getSuccessor());
				result.addTransition(trans.getSymbol(), ImmutableSet.of(predecessors), ImmutableSet.of(successors));
			}
		}
	}

	private void addSharedTransitionsHelper(final Transition<LETTER, PLACE> netTrans,
			final AutomatonTransition nwaTrans, final Set<PLACE> predecessors,
			final BoundedPetriNet<LETTER, PLACE> result) {
		predecessors.addAll(netTrans.getPredecessors());
		predecessors.add(nwaTrans.getPredecessor());

		final Set<PLACE> successors = new HashSet<>(netTrans.getSuccessors());
		successors.add(nwaTrans.getSuccessor());
		result.addTransition(netTrans.getSymbol(), ImmutableSet.of(predecessors), ImmutableSet.of(successors));
	}

	private void addPlacesAndStates(final BoundedPetriNet<LETTER, PLACE> result) {
		// add places of old net
		for (final PLACE oldPlace : mOperand.getPlaces()) {
			final boolean isInitial = mOperand.getInitialPlaces().contains(oldPlace);
			final boolean isAccepting = mOperand.getAcceptingPlaces().contains(oldPlace);
			final boolean newlyAdded = result.addPlace(oldPlace, isInitial, isAccepting);
			if (!newlyAdded) {
				throw new AssertionError("Input must not contain place twice.");
			}
		}

		// add states of automaton
		for (final PLACE state : mNwa.getStates()) {
			final boolean isInitial = mNwa.getInitialStates().contains(state);
			final boolean isAccepting = mNwa.isFinal(state);
			final boolean newlyAdded = result.addPlace(state, isInitial, isAccepting);
			if (!newlyAdded) {
				throw new UnsupportedOperationException(
						PetriNetUtils.generateStatesAndPlacesDisjointErrorMessage(state));
			}
		}
	}

	@Override
	public boolean checkResult(final CRSF stateFactory) throws AutomataLibraryException {
		mLogger.info("Testing correctness of prefixProduct");

		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> op1AsNwa =
				(new PetriNet2FiniteAutomaton<>(mServices, stateFactory, mOperand)).getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> resultAsNwa =
				(new PetriNet2FiniteAutomaton<>(mServices, stateFactory, mResult)).getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> nwaResult =
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
		private final PLACE mPredecessor;
		private final LETTER mLetter;
		private final PLACE mSuccessor;

		public AutomatonTransition(final PLACE predecessor, final LETTER letter, final PLACE successor) {
			mPredecessor = predecessor;
			mLetter = letter;
			mSuccessor = successor;
		}

		public PLACE getPredecessor() {
			return mPredecessor;
		}

		public LETTER getSymbol() {
			return mLetter;
		}

		public PLACE getSuccessor() {
			return mSuccessor;
		}
	}
}
