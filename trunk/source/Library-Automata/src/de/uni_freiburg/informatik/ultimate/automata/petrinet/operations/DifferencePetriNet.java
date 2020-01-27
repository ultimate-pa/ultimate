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
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.SimpleSuccessorTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.SuccessorTransitionProviderSplit;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import petruchio.sim.petrinettool.IPetriNet;

/**
 * Petri net for on-demand construction of difference.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class DifferencePetriNet<LETTER, PLACE> implements IPetriNetSuccessorProvider<LETTER, PLACE> {

	private static final String EXACTLY_ONE_STATE_OF_SUBTRAHEND = "query for successors must contain exactly one state of subtrahend";
	private static final String AT_MOST_ONE_STATE_OF_SUBTRAHEND = "query for successors must contain at most one state of subtrahend";
	private static final String EMPTY_INITIAL_ERROR_MESSAGE = "Subtrahend has no initial states! We could soundly return the minuend as result (implement this if required). However we presume that in most cases, such a subtrahend was passed accidentally";
	private final AutomataLibraryServices mServices;
	private final IPetriNetSuccessorProvider<LETTER, PLACE> mMinued;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> mSubtrahend;
	private final Map<ITransition<LETTER, PLACE>, ITransition<LETTER, PLACE>> mNew2Old = new HashMap<ITransition<LETTER, PLACE>, ITransition<LETTER, PLACE>>();
	private final HashRelation<ITransition<LETTER, PLACE>, ITransition<LETTER, PLACE>> mOld2New = new HashRelation<>();
	private final Map<ITransition<LETTER, PLACE>, PLACE> mNewTransition2AutomatonPredecessorState = new HashMap<>();
	private final Set<PLACE> mMinuendPlaces = new HashSet<>();
	private final Set<PLACE> mSubtrahendStates = new HashSet<>();
	private final NestedMap2<ITransition<LETTER, PLACE>, PLACE, ITransition<LETTER, PLACE>> mInputTransition2State2OutputTransition = new NestedMap2<>();
	private int mNumberOfConstructedTransitions = 0;
	// horrible hack to do a cast and store known transitions
	// 20200126 Matthias: We can get rid of this Map by using
	// information form mOld2New
	private final Map<ITransition<LETTER, PLACE>, Transition<LETTER, PLACE>> mTransitions = new HashMap<>();
	/**
	 * Letters for which the subtrahend DFA has a selfloop in every state. This
	 * set is provided by the user of {@link DifferencePetriNet} it can be an
	 * underapproximation of the letters that have a selfloop, we do not check
	 * if this set does really contain only universal loopers (i.e., we do
	 * not check if what the user provided was correct).
	 */
	private final Set<LETTER> mUniversalLoopers;

	private final SynchronizationInformation mSynchronizationInformation = new SynchronizationInformation();

	public DifferencePetriNet(final AutomataLibraryServices services,
			final IPetriNetSuccessorProvider<LETTER, PLACE> minued,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> subtrahend, final Set<LETTER> universalLoopers) {
		super();
		mServices = services;
		mMinued = minued;
		mSubtrahend = subtrahend;
		mUniversalLoopers = universalLoopers;
	}

	@Override
	public Set<PLACE> getInitialPlaces() {
		final Set<PLACE> result = new HashSet<>(mMinued.getInitialPlaces());
		final Iterator<PLACE> it = mSubtrahend.getInitialStates().iterator();
		if (!it.hasNext()) {
			throw new UnsupportedOperationException(EMPTY_INITIAL_ERROR_MESSAGE);
		}
		final PLACE automatonInitialState = it.next();
		result.add(automatonInitialState);
		if (it.hasNext()) {
			throw new IllegalArgumentException("subtrahend not deterministic");
		}
		if (mSubtrahend.isFinal(automatonInitialState)) {
			return Collections.emptySet();
		}
		mSubtrahendStates.add(automatonInitialState);
		for (final PLACE initialPlace : mMinued.getInitialPlaces()) {
			mMinuendPlaces.add(initialPlace);
		}
		return result;
	}

	@Override
	public Set<PLACE> getSuccessors(final ITransition<LETTER, PLACE> transition) {
		final Transition<LETTER, PLACE> casted = mTransitions.get(transition);
		if (casted == null) {
			throw new IllegalArgumentException("unknown transition " + transition);
		} else {
			return casted.getSuccessors();
		}
	}

	@Override
	public Set<PLACE> getPredecessors(final ITransition<LETTER, PLACE> transition) {
		final Transition<LETTER, PLACE> casted = mTransitions.get(transition);
		if (casted == null) {
			throw new IllegalArgumentException("unknown transition " + transition);
		} else {
			return casted.getPredecessors();
		}
	}

	/**
	 * @param places
	 *            Set of places where exactly one is a state of the subtrahend and
	 *            the others are places of the minuend.
	 */
	@Override
	public Collection<ISuccessorTransitionProvider<LETTER, PLACE>> getSuccessorTransitionProviders(
			final HashRelation<PLACE, PLACE> place2allowedSiblings) {
		if (place2allowedSiblings.isEmpty()) {
			return Collections.emptySet();
		}
//		assert (exactlyOneStateFromAutomaton(place2allowedSiblings)) : "not exactly one state from automaton";
		final HashRelation<Set<PLACE>, PLACE> mNetPredecessors2AutomatonPredecessors = new HashRelation<>();
		final Map<Set<PLACE>, ISuccessorTransitionProvider<LETTER, PLACE>> mNetPredecessors2TransitionProvider = new HashMap<>();
		for (final PLACE place : place2allowedSiblings.getDomain()) {
			if (mMinuendPlaces.contains(place)) {
				final HashRelation<PLACE, PLACE> tmp = new HashRelation<>();
				final Pair<Set<PLACE>, Set<PLACE>> split = split(place2allowedSiblings.getImage(place));
//				assert split.getSecond().size() <= 1 : "there can be at most one automaton successor";
				tmp.addAllPairs(place, split.getFirst());
				final Collection<ISuccessorTransitionProvider<LETTER, PLACE>> preds = mMinued.getSuccessorTransitionProviders(tmp);
				for (final ISuccessorTransitionProvider<LETTER, PLACE> stp : preds) {
					mNetPredecessors2AutomatonPredecessors.addAllPairs(stp.getPredecessorPlaces(), split.getSecond());
					mNetPredecessors2TransitionProvider.put(stp.getPredecessorPlaces(), stp);
				}
			} else if (mSubtrahendStates.contains(place)) {
				final Pair<Set<PLACE>, Set<PLACE>> split = split(place2allowedSiblings.getImage(place));
				assert split.getSecond().equals(Collections.singleton(place)) : "automata states cannot be siblings "
						+ place + " " + split.getSecond();
				final HashRelation<PLACE, PLACE> tmp = new HashRelation<>();
				for (final PLACE minuendAllowedSibling : split.getFirst()) {
					tmp.addAllPairs(minuendAllowedSibling, split.getFirst());
				}
				final Collection<ISuccessorTransitionProvider<LETTER, PLACE>> preds = mMinued.getSuccessorTransitionProviders(split.getFirst(), split.getFirst());
				for (final ISuccessorTransitionProvider<LETTER, PLACE> stp : preds) {
					mNetPredecessors2AutomatonPredecessors.addPair(stp.getPredecessorPlaces(), place);
					mNetPredecessors2TransitionProvider.put(stp.getPredecessorPlaces(), stp);
				}
			} else {
				throw new IllegalArgumentException("state does not exist");
			}
		}
//		PLACE automatonPredecessor = null;
//		Set<PLACE> automatonPredecessorSiblings = null;
//		final HashRelation<PLACE, PLACE> petriNetPredecessors = new HashRelation<>();
//		for (final Entry<PLACE, PLACE> entry : place2allowedSiblings.entrySet()) {
//			if (mMinuendPlaces.contains(entry.getKey())) {
//
//				petriNetPredecessors.addPair(entry.getKey(), entry.getValue());
//			} else if (mSubtrahendStates.contains(entry.getKey())) {
//				if (automatonPredecessor == null) {
//					automatonPredecessor = entry.getKey();
//					automatonPredecessorSiblings = entry.getValue();
//				} else {
//					throw new IllegalArgumentException(AT_MOST_ONE_STATE_OF_SUBTRAHEND);
//				}
//			}
//		}
//
		final List<ISuccessorTransitionProvider<LETTER, PLACE>> result = new ArrayList<>();
//		final Collection<ISuccessorTransitionProvider<LETTER, PLACE>> preds;
//		if (automatonPredecessor == null) {
//			preds = mMinued.getSuccessorTransitionProviders(petriNetPredecessors);
//		} else {
//			// do use transitions of *all* yet known places because the subtrahend
//			// predecessor could potentially have a transition with all of them.
//			// TODO 2018-10-21 Matthias: Optimization: Overapproximate candidates
//			// in Unfolding. Do not take all minuend places but only these where at
//			// least one corresponding place is in co-relation with automaton
//			// successor
//			preds = mMinued.getSuccessorTransitionProviders(mMinuendPlaces);
//		}

		final boolean useUniversalLoopersOptimization = (mUniversalLoopers != null);


		for (final Set<PLACE> predecessors : mNetPredecessors2AutomatonPredecessors.getDomain()) {
			final Set<PLACE> automatonPredecessors = mNetPredecessors2AutomatonPredecessors.getImage(predecessors);
			final ISuccessorTransitionProvider<LETTER, PLACE> pred = mNetPredecessors2TransitionProvider.get(predecessors);
			if (useUniversalLoopersOptimization) {
				final SuccessorTransitionProviderSplit<LETTER, PLACE> split = new SuccessorTransitionProviderSplit<>(
						pred, mUniversalLoopers, mMinued);
				if (split.getSuccTransProviderLetterInSet() != null) {
					// copy from minuend, no need to synchronize
					final List<ITransition<LETTER, PLACE>> transitions = new ArrayList<>();
					for (final ITransition<LETTER, PLACE> trans : split.getSuccTransProviderLetterInSet().getTransitions()) {
						final Set<PLACE> transitionPredecessors = mMinued.getPredecessors(trans);
//						if (!mMinuendPlaces.containsAll(transitionPredecessors)) {
//							// not all predecessors places of transition are
//							// yet constructed, maybe this transition is dead
//							continue;
//						}
						if (DataStructureUtils.haveNonEmptyIntersection(transitionPredecessors, place2allowedSiblings.getDomain())) {
							transitions.add(trans);
						} else {
							// do nothing
							// must not add, no corresponding place
							// transition will be considered if one of the
							// predecessor places is considered
						}
					}
					if (!transitions.isEmpty()) {
						result.add(new SimpleSuccessorTransitionProviderWithUsageInformation(transitions, mMinued));
					}

				}
				if (split.getSuccTransProviderLetterNotInSet() != null) {
//					for (final PLACE automatonPredecessor : automatonPredecessors)
//					if (automatonPredecessor != null) {
//						result.add(new DifferenceSuccessorTransitionProvider(split.getSuccTransProviderLetterNotInSet(), automatonPredecessor));
//					} else {
						for (final PLACE yetConstructedState : automatonPredecessors) {
							result.add(new DifferenceSuccessorTransitionProvider(split.getSuccTransProviderLetterNotInSet(), yetConstructedState));
						}
//					}
				}
			} else {
//				if (automatonPredecessor == null) {
//					throw new IllegalArgumentException(EXACTLY_ONE_STATE_OF_SUBTRAHEND);
//				}
				for (final PLACE yetConstructedState : automatonPredecessors) {
					result.add(new DifferenceSuccessorTransitionProvider(pred, yetConstructedState));
				}
			}
		}
		return result;
	}

	private boolean exactlyOneStateFromAutomaton(final HashRelation<PLACE, PLACE> place2allowedSiblings) {
		final Pair<Set<PLACE>, Set<PLACE>> split = split(place2allowedSiblings.getDomain());
		return split.getSecond().size() == 1;
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
	public boolean isAccepting(final Marking<LETTER, PLACE> marking) {
		final Set<PLACE> petriNetPlaces = new HashSet<>();
		for (final PLACE place : marking) {
			if (mMinuendPlaces.contains(place)) {
				petriNetPlaces.add(place);
			}
		}
		final Marking<LETTER, PLACE> filteredMarking = new Marking<>(petriNetPlaces);
		return mMinued.isAccepting(filteredMarking);
	}

	private class DifferenceSuccessorTransitionProvider implements ISuccessorTransitionProvider<LETTER, PLACE> {
		private final ISuccessorTransitionProvider<LETTER, PLACE> mPetriNetPredecessors;
		private final PLACE mAutomatonPredecessor;
		private final LinkedHashSet<PLACE> mAllPredecessors;

		public DifferenceSuccessorTransitionProvider(
				final ISuccessorTransitionProvider<LETTER, PLACE> petriNetPredecessors,
				final PLACE automatonPredecessor) {
			super();
			mPetriNetPredecessors = petriNetPredecessors;
			mAutomatonPredecessor = automatonPredecessor;
			mAllPredecessors = new LinkedHashSet<>(petriNetPredecessors.getPredecessorPlaces());
			mAllPredecessors.add(automatonPredecessor);
		}

		@Override
		public Set<PLACE> getPredecessorPlaces() {
			return Collections.unmodifiableSet(mAllPredecessors);
		}

		@Override
		public Collection<ITransition<LETTER, PLACE>> getTransitions() {
			final List<ITransition<LETTER, PLACE>> result = new ArrayList<>();
			for (final ITransition<LETTER, PLACE> inputTransition : mPetriNetPredecessors.getTransitions()) {
				final ITransition<LETTER, PLACE> outputTransition = getOrConstructTransition(inputTransition,
						mAutomatonPredecessor);
				if (outputTransition != null) {
					result.add(outputTransition);
				}
			}
			return result;
		}

		/**
		 *
		 * @return null iff subtrahend successor is accepting which means that we do not
		 *         want such a transition in our resulting Petri net.
		 */
		private ITransition<LETTER, PLACE> getOrConstructTransition(final ITransition<LETTER, PLACE> inputTransition,
				final PLACE automatonPredecessor) {
			ITransition<LETTER, PLACE> result = mInputTransition2State2OutputTransition.get(inputTransition,
					automatonPredecessor);
			if (result == null) {
				OutgoingInternalTransition<LETTER, PLACE> subtrahendSucc;
				{
					final Iterable<OutgoingInternalTransition<LETTER, PLACE>> subtrahendSuccs = mSubtrahend
							.internalSuccessors(automatonPredecessor, inputTransition.getSymbol());
					final Iterator<OutgoingInternalTransition<LETTER, PLACE>> it = subtrahendSuccs.iterator();
					if (!it.hasNext()) {
						throw new IllegalArgumentException("Subtrahend not total.");
					}
					subtrahendSucc = it.next();
					if (it.hasNext()) {
						throw new IllegalArgumentException("Subtrahend not deterministic.");
					}
				}
				if (automatonPredecessor != subtrahendSucc.getSucc()) {
					mSynchronizationInformation.getChangerLetters().add(inputTransition.getSymbol());
					mSynchronizationInformation.getStateChangers().addPair(inputTransition, automatonPredecessor);
				} else {
					mSynchronizationInformation.getSelfloops().addPair(inputTransition, automatonPredecessor);
				}
				mSynchronizationInformation.getContributingTransitions().add(inputTransition);
				if (mSubtrahend.isFinal(subtrahendSucc.getSucc())) {
					return null;
				} else {
					final Set<PLACE> successors = new LinkedHashSet<>();
					for (final PLACE petriNetSuccessor : mMinued.getSuccessors(inputTransition)) {
						// possibly first time that we saw this place, add
						mMinuendPlaces.add(petriNetSuccessor);
						successors.add(petriNetSuccessor);
					}
					mSubtrahendStates.add(subtrahendSucc.getSucc());
					successors.add(subtrahendSucc.getSucc());

					final int totalOrderId = mNumberOfConstructedTransitions;
					mNumberOfConstructedTransitions++;
					result = new Transition<>(inputTransition.getSymbol(), mAllPredecessors, successors, totalOrderId);
					mInputTransition2State2OutputTransition.put(inputTransition, automatonPredecessor, result);
					mTransitions.put(result, (Transition<LETTER, PLACE>) result);
					final ITransition<LETTER, PLACE> valueBefore = mNew2Old.put(result, inputTransition);
					assert valueBefore == null : "Cannot add transition twice.";
				}
			}
			return result;
		}
	}




	BoundedPetriNet<LETTER, PLACE> getYetConstructedPetriNet() {
		final BoundedPetriNet<LETTER, PLACE> result = new BoundedPetriNet<>(mServices, mMinued.getAlphabet(), false);
		for (final PLACE place : mMinuendPlaces) {
			result.addPlace(place, mMinued.getInitialPlaces().contains(place), mMinued.isAccepting(place));
		}
		for (final PLACE place : mSubtrahendStates) {
			result.addPlace(place, mSubtrahend.isInitial(place), false);
		}
		for (final Entry<ITransition<LETTER, PLACE>, Transition<LETTER, PLACE>> entry : mTransitions.entrySet()) {
			result.addTransition(entry.getValue().getSymbol(), entry.getValue().getPredecessors(),
					entry.getValue().getSuccessors());
		}
		return result;
	}

	/**
	 * @return Mapping from new transitions (i.e., transitions of the resulting
	 *         difference) to old transitions (i.e., transitions of the minuend).
	 */
	Map<ITransition<LETTER, PLACE>, ITransition<LETTER, PLACE>> getTransitionBacktranslation() {
		return mNew2Old;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mMinued.getAlphabet();
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
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
		} else {
			return mMinued.isAccepting(place);
		}
	}

	@Override
	public Collection<ISuccessorTransitionProvider<LETTER, PLACE>> getSuccessorTransitionProviders(
			final Set<PLACE> placesOfNewConditions, final Set<PLACE> correlatedPlaces) {
		throw new IllegalArgumentException("getSuccessorTransitionProviders with the given arguments works only for " + IPetriNet.class.getName());
	}

	public SynchronizationInformation getSynchronizationInformation() {
		return mSynchronizationInformation;
	}

	public class SynchronizationInformation {
		/**
		 * Letters for which the subtrahend DFA actually has a transition that
		 * changes the state. In on-demand constructions, this information can be
		 * more precise than mUniversalLoopers because the user cannot foresee the
		 * construction process.
		 */
		private final Set<LETTER> mChangerLetters = new HashSet<>();

		private final HashRelation<ITransition<LETTER, PLACE>, PLACE> mSelfloops = new HashRelation<>();
		private final HashRelation<ITransition<LETTER, PLACE>, PLACE> mStateChangers = new HashRelation<>();

		private final Set<ITransition<LETTER, PLACE>> mContributingTransitions = new HashSet<>();

		public Set<LETTER> getChangerLetters() {
			return mChangerLetters;
		}
		public HashRelation<ITransition<LETTER, PLACE>, PLACE> getSelfloops() {
			return mSelfloops;
		}
		public HashRelation<ITransition<LETTER, PLACE>, PLACE> getStateChangers() {
			return mStateChangers;
		}
		public Set<ITransition<LETTER, PLACE>> getContributingTransitions() {
			return mContributingTransitions;
		}

		public SynchronizationInformation filter(final Set<ITransition<LETTER, PLACE>> transitions) {
			final SynchronizationInformation result = new SynchronizationInformation();
			result.getChangerLetters().addAll(mChangerLetters);
			for (final Entry<ITransition<LETTER, PLACE>, HashSet<PLACE>> entry : mSelfloops.entrySet()) {
				result.getSelfloops().addAllPairs(entry.getKey(), entry.getValue());
			}
			for (final Entry<ITransition<LETTER, PLACE>, HashSet<PLACE>> entry : mStateChangers.entrySet()) {
				result.getStateChangers().addAllPairs(entry.getKey(), entry.getValue());
			}
			result.getContributingTransitions().addAll(transitions);
			return result;
		}
	}

	private class SimpleSuccessorTransitionProviderWithUsageInformation
			extends SimpleSuccessorTransitionProvider<LETTER, PLACE> {

		public SimpleSuccessorTransitionProviderWithUsageInformation(
				final Collection<ITransition<LETTER, PLACE>> transitions,
				final IPetriNetSuccessorProvider<LETTER, PLACE> net) {
			super(transitions, net);
		}

		@Override
		public Collection<ITransition<LETTER, PLACE>> getTransitions() {
			final Collection<ITransition<LETTER, PLACE>> transitions = new ArrayList<>();
			for (final ITransition<LETTER, PLACE> inputTransition : super.getTransitions()) {
				final ITransition<LETTER, PLACE> resultTransition = getOrConstructTransitionCopy(inputTransition);
				transitions.add(resultTransition);
			}
			return transitions;
		}

		private ITransition<LETTER, PLACE> getOrConstructTransitionCopy(final ITransition<LETTER, PLACE> inputTransition) {
			ITransition<LETTER, PLACE> result = mInputTransition2State2OutputTransition.get(inputTransition, null);
			if (result == null) {
//				assert (mMinuendPlaces.containsAll(mMinued.getPredecessors(inputTransition))) : "missing predecessor";
				final Set<PLACE> successors = new LinkedHashSet<>();
				for (final PLACE petriNetSuccessor : mMinued.getSuccessors(inputTransition)) {
					// possibly first time that we saw this place, add
					mMinuendPlaces.add(petriNetSuccessor);
					successors.add(petriNetSuccessor);
				}
				final int totalOrderId = mNumberOfConstructedTransitions;
				mNumberOfConstructedTransitions++;
				result = new Transition<>(inputTransition.getSymbol(), mMinued.getPredecessors(inputTransition), successors,
						totalOrderId);
				mInputTransition2State2OutputTransition.put(inputTransition, null, result);
				mTransitions.put(result, (Transition<LETTER, PLACE>) result);
				final ITransition<LETTER, PLACE> valueBefore = mNew2Old.put(result, inputTransition);
				assert valueBefore == null : "Cannot add transition twice.";
				mSynchronizationInformation.getContributingTransitions().add(inputTransition);
			}
			return result;
		}

	}

}
