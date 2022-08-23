/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.SimpleSuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.SuccessorTransitionProviderSplit;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Petri net for on-demand construction of difference.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class DifferencePetriNet<LETTER, PLACE> implements IPetriNetSuccessorProvider<LETTER, PLACE> {
	private final AutomataLibraryServices mServices;
	private final IPetriNetSuccessorProvider<LETTER, PLACE> mMinuend;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> mSubtrahend;
	private final Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> mNew2Old = new HashMap<>();
	private final Map<Transition<LETTER, PLACE>, PLACE> mNewTransition2AutomatonPredecessorState = new HashMap<>();
	private final HashRelation<Transition<LETTER, PLACE>, PLACE> mBlockingConfigurations = new HashRelation<>();
	private final Set<PLACE> mMinuendPlaces = new HashSet<>();
	private final Set<PLACE> mSubtrahendStates = new HashSet<>();
	private final NestedMap2<Transition<LETTER, PLACE>, PLACE, Transition<LETTER, PLACE>> mInputTransition2State2OutputTransition =
			new NestedMap2<>();
	private int mNumberOfConstructedTransitions;
	/**
	 * Letters for which the subtrahend DFA has a selfloop in every state. This set is provided by the user of
	 * {@link DifferencePetriNet} it can be an underapproximation of the letters that have a selfloop, we do not check
	 * if this set does really contain only universal loopers (i.e., we do not check if what the user provided was
	 * correct).
	 */
	private final Set<LETTER> mUniversalLoopers;
	private final BoundedPetriNet<LETTER, PLACE> mYetConstructedResult;

	public DifferencePetriNet(final AutomataLibraryServices services,
			final IPetriNetSuccessorProvider<LETTER, PLACE> minued,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> subtrahend,
			final Set<LETTER> universalLoopers) {
		super();
		mServices = services;
		mMinuend = minued;
		mSubtrahend = subtrahend;
		mUniversalLoopers = universalLoopers;
		mYetConstructedResult = new BoundedPetriNet<>(mServices, mMinuend.getAlphabet(), false);
	}

	@Override
	public Set<PLACE> getInitialPlaces() {
		final Iterator<PLACE> it = mSubtrahend.getInitialStates().iterator();
		if (!it.hasNext()) {
			throw new UnsupportedOperationException(
					"Subtrahend has no initial states! We could soundly return the minuend as result (implement this if required). "
							+ "However we presume that in most cases, such a subtrahend was passed accidentally");
		}
		final Set<PLACE> result = new HashSet<>(mMinuend.getInitialPlaces());
		final PLACE automatonInitialState = it.next();
		result.add(automatonInitialState);
		if (it.hasNext()) {
			throw new IllegalArgumentException("subtrahend not deterministic");
		}
		if (mSubtrahend.isFinal(automatonInitialState)) {
			return Collections.emptySet();
		}
		addSubtrahendState(automatonInitialState);
		for (final PLACE initialPlace : mMinuend.getInitialPlaces()) {
			addMinuendPlace(initialPlace);
		}
		return result;
	}

	private void addMinuendPlace(final PLACE newMinuendPlace) {
		final boolean newlyAdded = mMinuendPlaces.add(newMinuendPlace);
		if (newlyAdded) {
			final boolean isInitial = mMinuend.getInitialPlaces().contains(newMinuendPlace);
			final boolean isAccepting = mMinuend.isAccepting(newMinuendPlace);
			final boolean newlyAddedToYcr = mYetConstructedResult.addPlace(newMinuendPlace, isInitial, isAccepting);
			if (!newlyAddedToYcr) {
				throw new AssertionError("Must not add place twice: " + newMinuendPlace);
			}
		}
	}

	private void addSubtrahendState(final PLACE newSubtrahendState) {
		final boolean newlyAdded = mSubtrahendStates.add(newSubtrahendState);
		if (newlyAdded) {
			final boolean isInitial = mSubtrahend.isInitial(newSubtrahendState);
			final boolean newlyAddedToYcr = mYetConstructedResult.addPlace(newSubtrahendState, isInitial, false);
			if (!newlyAddedToYcr) {
				throw new AssertionError("Must not add place twice: " + newSubtrahendState);
			}
		}
	}

	@Override
	public Collection<ISuccessorTransitionProvider<LETTER, PLACE>>
			getSuccessorTransitionProviders(final Set<PLACE> mustPlaces, final Set<PLACE> mayPlaces) {
		if (mustPlaces.isEmpty()) {
			return Collections.emptySet();
		}
		assert (mayPlaces.containsAll(mustPlaces)) : "some must place is not may place";
		final Pair<Set<PLACE>, Set<PLACE>> splitMust = split(mustPlaces);
		final Set<PLACE> minuendMustPlaces = splitMust.getFirst();
		final Set<PLACE> subtrahendMustStates = splitMust.getSecond();
		final Pair<Set<PLACE>, Set<PLACE>> splitMay = split(mayPlaces);
		final Set<PLACE> minuendMayPlaces = splitMay.getFirst();
		final Set<PLACE> subtrahendMayStates = splitMay.getSecond();
		final Collection<ISuccessorTransitionProvider<LETTER, PLACE>> minuendStps;
		if (subtrahendMustStates.isEmpty()) {
			minuendStps = mMinuend.getSuccessorTransitionProviders(minuendMustPlaces, minuendMayPlaces);
		} else {
			minuendStps = mMinuend.getSuccessorTransitionProviders(minuendMayPlaces, minuendMayPlaces);
		}

		final boolean useUniversalLoopersOptimization = (mUniversalLoopers != null);
		final List<ISuccessorTransitionProvider<LETTER, PLACE>> result = new ArrayList<>();
		for (final ISuccessorTransitionProvider<LETTER, PLACE> minuendStp : minuendStps) {
			// TODO: Compute on-demand
			final boolean emtpyIntersectionWithMinuendMustPlaces =
					DataStructureUtils.haveEmptyIntersection(minuendStp.getPredecessorPlaces(), minuendMustPlaces);
			if (useUniversalLoopersOptimization) {
				final SuccessorTransitionProviderSplit<LETTER, PLACE> split =
						new SuccessorTransitionProviderSplit<>(minuendStp, mUniversalLoopers);
				if (split.getSuccTransProviderLetterInSet() != null) {
					// copy from minuend, no need to synchronize
					if (emtpyIntersectionWithMinuendMustPlaces) {
						// do nothing
						// must not add, no corresponding place
						// transition will be considered if one of the
						// predecessor places is considered
					} else {
						result.add(new SimpleSuccessorTransitionProviderWithUsageInformation(
								split.getSuccTransProviderLetterInSet().getTransitions()));
					}
				}
				if (split.getSuccTransProviderLetterNotInSet() != null) {
					Set<PLACE> automatonPredecessorsToConsider;
					if (emtpyIntersectionWithMinuendMustPlaces) {
						automatonPredecessorsToConsider = subtrahendMustStates;
					} else {
						automatonPredecessorsToConsider = subtrahendMayStates;
					}
					for (final PLACE automatonPredecessor : automatonPredecessorsToConsider) {
						result.add(new DifferenceSuccessorTransitionProvider(split.getSuccTransProviderLetterNotInSet(),
								automatonPredecessor));
					}
				}
			} else {
				Set<PLACE> automatonPredecessorsToConsider;
				if (emtpyIntersectionWithMinuendMustPlaces) {
					automatonPredecessorsToConsider = subtrahendMustStates;
				} else {
					automatonPredecessorsToConsider = subtrahendMayStates;
				}
				for (final PLACE automatonPredecessor : automatonPredecessorsToConsider) {
					result.add(new DifferenceSuccessorTransitionProvider(minuendStp, automatonPredecessor));
				}
			}
		}
		return result;
	}

	private Pair<Set<PLACE>, Set<PLACE>> split(final Set<PLACE> places) {
		final Pair<Set<PLACE>, Set<PLACE>> result = new Pair<>(new HashSet<>(), new HashSet<>());
		for (final PLACE place : places) {
			if (mMinuendPlaces.contains(place)) {
				result.getFirst().add(place);
			} else if (mSubtrahendStates.contains(place)) {
				result.getSecond().add(place);
			}
		}
		return result;
	}

	@Override
	public boolean isAccepting(final Marking<PLACE> marking) {
		final Set<PLACE> petriNetPlaces = new HashSet<>();
		for (final PLACE place : marking) {
			if (mMinuendPlaces.contains(place)) {
				petriNetPlaces.add(place);
			}
		}
		final Marking<PLACE> filteredMarking = new Marking<>(ImmutableSet.of(petriNetPlaces));
		return mMinuend.isAccepting(filteredMarking);
	}

	private class DifferenceSuccessorTransitionProvider implements ISuccessorTransitionProvider<LETTER, PLACE> {
		private final ISuccessorTransitionProvider<LETTER, PLACE> mPetriNetPredecessors;
		private final PLACE mAutomatonPredecessor;
		private final ImmutableSet<PLACE> mAllPredecessors;

		public DifferenceSuccessorTransitionProvider(
				final ISuccessorTransitionProvider<LETTER, PLACE> petriNetPredecessors,
				final PLACE automatonPredecessor) {
			super();
			mPetriNetPredecessors = petriNetPredecessors;
			mAutomatonPredecessor = automatonPredecessor;
			final Set<PLACE> predecessors = new LinkedHashSet<>(petriNetPredecessors.getPredecessorPlaces());
			predecessors.add(automatonPredecessor);
			mAllPredecessors = ImmutableSet.of(predecessors);
		}

		@Override
		public Set<PLACE> getPredecessorPlaces() {
			return mAllPredecessors;
		}

		@Override
		public Collection<Transition<LETTER, PLACE>> getTransitions() {
			final List<Transition<LETTER, PLACE>> result = new ArrayList<>();
			for (final Transition<LETTER, PLACE> inputTransition : mPetriNetPredecessors.getTransitions()) {
				final Transition<LETTER, PLACE> outputTransition =
						getOrConstructTransition(inputTransition, mAutomatonPredecessor);
				if (outputTransition != null) {
					result.add(outputTransition);
				}
			}
			return result;
		}

		/**
		 *
		 * @return null iff subtrahend successor is accepting which means that we do not want such a transition in our
		 *         resulting Petri net.
		 */
		private Transition<LETTER, PLACE> getOrConstructTransition(final Transition<LETTER, PLACE> inputTransition,
				final PLACE automatonPredecessor) {
			Transition<LETTER, PLACE> result =
					mInputTransition2State2OutputTransition.get(inputTransition, automatonPredecessor);
			if (result == null) {
				final PLACE automatonSuccessor = NestedWordAutomataUtils.getSuccessorState(mSubtrahend,
						automatonPredecessor, inputTransition.getSymbol());
				if (mSubtrahend.isFinal(automatonSuccessor)) {
					mBlockingConfigurations.addPair(inputTransition, automatonPredecessor);
					return null;
				}
				final Set<PLACE> successors = new LinkedHashSet<>();
				for (final PLACE petriNetSuccessor : inputTransition.getSuccessors()) {
					// possibly first time that we saw this place, add
					addMinuendPlace(petriNetSuccessor);
					successors.add(petriNetSuccessor);
				}
				addSubtrahendState(automatonSuccessor);
				successors.add(automatonSuccessor);

				final int totalOrderId = mNumberOfConstructedTransitions;
				mNumberOfConstructedTransitions++;
				result = mYetConstructedResult.addTransition(inputTransition.getSymbol(), mAllPredecessors,
						ImmutableSet.of(successors), totalOrderId);
				mInputTransition2State2OutputTransition.put(inputTransition, automatonPredecessor, result);
				mNewTransition2AutomatonPredecessorState.put(result, automatonPredecessor);
				final Transition<LETTER, PLACE> valueBefore = mNew2Old.put(result, inputTransition);
				assert valueBefore == null : "Cannot add transition twice.";
			}
			return result;
		}
	}

	public BoundedPetriNet<LETTER, PLACE> getYetConstructedPetriNet() {
		return mYetConstructedResult;
	}

	/**
	 * @return Mapping from new transitions (i.e., transitions of the resulting difference) to old transitions (i.e.,
	 *         transitions of the minuend).
	 */
	public Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> getTransitionBacktranslation() {
		return Collections.unmodifiableMap(mNew2Old);
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mMinuend.getAlphabet();
	}

	@Override
	public int size() {
		// we do not provide size during on-demand construction
		return -1;
	}

	@Override
	public String sizeInformation() {
		return "will be constructed on-demand";
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isAccepting(final PLACE place) {
		if (mSubtrahendStates.contains(place)) {
			return false;
		}
		return mMinuend.isAccepting(place);
	}

	/**
	 * DifferenceSynchronizationInformation for all reachable transitions.
	 */
	public DifferenceSynchronizationInformation<LETTER, PLACE> computeDifferenceSynchronizationInformation() {
		return computeDifferenceSynchronizationInformation(mNew2Old.keySet(), false);
	}

	/**
	 * DifferenceSynchronizationInformation for a restricted set of transitions. This is useful if you want to restrict
	 * the result of an {@link Difference} operation to the set of vital transitions. TODO 2020-02-01 Matthias: Warning
	 * this information is not yet optimal. Assume we have a transition-state pair that is blocking but its preset is
	 * never reachable in the result of the Difference operation, then the entry in "blockingTransitions" is useless and
	 * might prevent an efficient synchronization of selfloops. However, I expect that the costs for a corresponding
	 * optimization are probably high and the gain is low.
	 */
	public DifferenceSynchronizationInformation<LETTER, PLACE> computeDifferenceSynchronizationInformation(
			final Set<Transition<LETTER, PLACE>> transitionSubset, final boolean vitalityPreserved) {
		final Set<LETTER> changerLetters = new HashSet<>();
		final HashRelation<Transition<LETTER, PLACE>, PLACE> selfloops = new HashRelation<>();
		final HashRelation<Transition<LETTER, PLACE>, PLACE> stateChangers = new HashRelation<>();
		final HashRelation<Transition<LETTER, PLACE>, PLACE> blockingTransitions = new HashRelation<>();
		final Set<Transition<LETTER, PLACE>> contributingTransitions = new HashSet<>();
		for (final Transition<LETTER, PLACE> transition : mNew2Old.keySet()) {
			final Transition<LETTER, PLACE> minuendTransition = mNew2Old.get(transition);
			assert minuendTransition != null : "Unknown transition: " + transition;
			final PLACE automatonPredecessor = mNewTransition2AutomatonPredecessorState.get(transition);
			if (automatonPredecessor == null) {
				// this transition is not synchronized with the automaton
				if (transitionSubset.contains(transition)) {
					contributingTransitions.add(minuendTransition);
				}
				continue;
			}
			final PLACE automatonSuccessor = NestedWordAutomataUtils.getSuccessorState(mSubtrahend,
					automatonPredecessor, transition.getSymbol());
			final boolean isSelfloop = (automatonPredecessor.equals(automatonSuccessor));
			if (!transitionSubset.contains(transition)) {
				if (!isSelfloop) {
					blockingTransitions.addPair(minuendTransition, automatonPredecessor);
					changerLetters.add(minuendTransition.getSymbol());
				} else {
					// do nothing
				}
			} else {
				contributingTransitions.add(minuendTransition);
				if (isSelfloop) {
					selfloops.addPair(minuendTransition, automatonPredecessor);
				} else {
					stateChangers.addPair(minuendTransition, automatonPredecessor);
					changerLetters.add(minuendTransition.getSymbol());
				}
			}
		}
		blockingTransitions.addAll(mBlockingConfigurations);
		for (final Transition<LETTER, PLACE> trans : mBlockingConfigurations.getDomain()) {
			changerLetters.add(trans.getSymbol());
		}
		return new DifferenceSynchronizationInformation<>(changerLetters, selfloops, stateChangers,
				contributingTransitions, blockingTransitions, true, vitalityPreserved);
	}

	private class SimpleSuccessorTransitionProviderWithUsageInformation
			extends SimpleSuccessorTransitionProvider<LETTER, PLACE> {

		public SimpleSuccessorTransitionProviderWithUsageInformation(
				final Collection<Transition<LETTER, PLACE>> transitions) {
			super(transitions);
		}

		@Override
		public Collection<Transition<LETTER, PLACE>> getTransitions() {
			final Collection<Transition<LETTER, PLACE>> transitions = new ArrayList<>();
			for (final Transition<LETTER, PLACE> inputTransition : super.getTransitions()) {
				final Transition<LETTER, PLACE> resultTransition = getOrConstructTransitionCopy(inputTransition);
				transitions.add(resultTransition);
			}
			return transitions;
		}

		private Transition<LETTER, PLACE>
				getOrConstructTransitionCopy(final Transition<LETTER, PLACE> inputTransition) {
			Transition<LETTER, PLACE> result = mInputTransition2State2OutputTransition.get(inputTransition, null);
			if (result == null) {
				final Set<PLACE> successors = new LinkedHashSet<>();
				for (final PLACE petriNetSuccessor : inputTransition.getSuccessors()) {
					// possibly first time that we saw this place, add
					addMinuendPlace(petriNetSuccessor);
					successors.add(petriNetSuccessor);
				}
				final int totalOrderId = mNumberOfConstructedTransitions;
				mNumberOfConstructedTransitions++;
				result = mYetConstructedResult.addTransition(inputTransition.getSymbol(),
						inputTransition.getPredecessors(), ImmutableSet.of(successors), totalOrderId);
				mInputTransition2State2OutputTransition.put(inputTransition, null, result);
				final Transition<LETTER, PLACE> valueBefore = mNew2Old.put(result, inputTransition);
				assert valueBefore == null : "Cannot add transition twice.";
			}
			return result;
		}

	}
}
