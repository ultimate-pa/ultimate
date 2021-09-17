/*
 * Copyright (C) 2019 Elisabeth Schanno
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 Dennis Wölfing
 * Copyright (C) 2019-2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.CopySubnet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Performs a form of Lipton reduction on Petri nets. This reduction fuses sequences of transition into one, if given
 * independence properties ("left / right mover") are satisfied w.r.t. to all concurrent transitions.
 *
 * See "Reduction: a method of proving properties of parallel programs" (https://dl.acm.org/doi/10.1145/361227.361234)
 *
 * Our implementation here also performs choice (or "parallel") compositions of transitions with the same pre- and
 * post-sets.
 *
 * @author Elisabeth Schanno
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters labeling the net's transitions.
 * @param <P>
 *            The type of places in the net.
 */
public class LiptonReduction<L, P> {
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;

	private final ICompositionFactory<L> mCompositionFactory;
	private final IPostScriptChecker<L, P> mStuckPlaceChecker;
	private final ICopyPlaceFactory<P> mPlaceFactory;
	private final IIndependenceRelation<Set<P>, L> mMoverCheck;
	private final IIndependenceCache<?, L> mIndependenceCache;

	private final BoundedPetriNet<L, P> mPetriNet;
	private BranchingProcess<L, P> mBranchingProcess;
	private CoenabledRelation<L, P> mCoEnabledRelation;

	private final HashRelation<Event<L, P>, Event<L, P>> mCutOffs = new HashRelation<>();
	private final Map<ITransition<L, P>, ITransition<L, P>> mNewToOldTransitions = new HashMap<>();

	private BoundedPetriNet<L, P> mResult;
	private final LiptonReductionStatisticsGenerator mStatistics = new LiptonReductionStatisticsGenerator();

	private final Map<ITransition<L, P>, List<ITransition<L, P>>> mSequentialCompositions = new HashMap<>();
	private final Map<ITransition<L, P>, List<ITransition<L, P>>> mChoiceCompositions = new HashMap<>();

	/**
	 * Performs Lipton reduction on the given Petri net.
	 *
	 * @param services
	 *            A {@link AutomataLibraryServices} instance.
	 * @param petriNet
	 *            The Petri Net on which the Lipton reduction should be performed.
	 * @param compositionFactory
	 *            An {@link ICompositionFactory} capable of performing compositions for the given alphabet.
	 * @param placeFactory
	 *            An {@link ICopyPlaceFactory} capable of creating places for the given Petri net.
	 * @param independenceRelation
	 *            The independence relation used for mover checks.
	 * @param stuckPlaceChecker
	 *            An {@link IPostScriptChecker}.
	 */
	public LiptonReduction(final AutomataLibraryServices services, final BoundedPetriNet<L, P> petriNet,
			final ICompositionFactory<L> compositionFactory, final ICopyPlaceFactory<P> placeFactory,
			final IIndependenceRelation<Set<P>, L> independenceRelation,
			final IPostScriptChecker<L, P> stuckPlaceChecker, final IIndependenceCache<?, L> cache) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(LiptonReduction.class);
		mCompositionFactory = compositionFactory;
		mPlaceFactory = placeFactory;
		mMoverCheck = independenceRelation;
		mPetriNet = petriNet;
		mStuckPlaceChecker = stuckPlaceChecker;
		mIndependenceCache = cache;
	}

	/**
	 * Performs the Lipton Reduction. Needs to be called once before using any other functions.
	 *
	 * @throws PetriNetNot1SafeException
	 *             if Petri Net is not 1-safe.
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled.
	 */
	public void performReduction() throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		mStatistics.start(LiptonReductionStatisticsDefinitions.ReductionTime);
		mStatistics.collectInitialStatistics(mPetriNet);
		mLogger.info("Starting Lipton reduction on Petri net that " + mPetriNet.sizeInformation());

		try {
			BoundedPetriNet<L, P> resultCurrentIteration = CopySubnet.copy(mServices, mPetriNet,
					new HashSet<>(mPetriNet.getTransitions()), mPetriNet.getAlphabet(), true);

			// TODO Why call FinitePrefix and not PetriNetUnfolder directly?
			mBranchingProcess = new FinitePrefix<>(mServices, resultCurrentIteration).getResult();
			mBranchingProcess.getEvents().stream().filter(Event::isCutoffEvent)
					.forEach(e -> mCutOffs.addPair(e.getCompanion(), e));
			mCoEnabledRelation = CoenabledRelation.fromBranchingProcess(mBranchingProcess);

			final int coEnabledRelationSize = mCoEnabledRelation.size();
			mLogger.info("Number of co-enabled transitions " + coEnabledRelationSize);
			mStatistics.setCoEnabledTransitionPairs(coEnabledRelationSize);

			BoundedPetriNet<L, P> resultLastIteration;
			do {
				mStatistics.reportFixpointIteration();
				resultLastIteration = resultCurrentIteration;

				// TODO decide on best ordering (e.g. choice at the beginning?)
				// TODO add / allow more rules, e.g. SynthesizeLockRule
				resultCurrentIteration = sequenceRule(resultLastIteration);
				resultCurrentIteration = choiceRuleWrapper(resultCurrentIteration);
			} while (resultLastIteration.getTransitions().size() != resultCurrentIteration.getTransitions().size());
			mResult = resultCurrentIteration;

			mLogger.info("Total number of compositions: "
					+ mStatistics.getValue(LiptonReductionStatisticsDefinitions.TotalNumberOfCompositions));
		} catch (final AutomataOperationCanceledException | ToolchainCanceledException ce) {
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(getClass(), generateTimeoutMessage(mPetriNet));
			ce.addRunningTaskInfo(runningTaskInfo);
			throw ce;
		} finally {
			mStatistics.stop(LiptonReductionStatisticsDefinitions.ReductionTime);
		}

		mStatistics.collectFinalStatistics(mResult);
	}

	private String generateTimeoutMessage(final BoundedPetriNet<L, P> petriNet) {
		if (mCoEnabledRelation == null) {
			return "applying " + getClass().getSimpleName() + " to Petri net that " + petriNet.sizeInformation();
		}
		return "applying " + getClass().getSimpleName() + " to Petri net that " + petriNet.sizeInformation() + " and "
				+ mCoEnabledRelation.size() + " co-enabled transitions pairs.";
	}

	private void transferMoverProperties(final L composition, final L t1, final L t2) {
		if (mIndependenceCache != null) {
			mIndependenceCache.mergeIndependencies(t1, t2, composition);
		}
	}

	/**
	 * @deprecated This wrapper is only supposed to exist temporarily
	 */
	@Deprecated(since = "2021-09-15")
	private BoundedPetriNet<L, P> synthesizeLockRuleWrapper(final BoundedPetriNet<L, P> petriNet) {
		final BoundedPetriNet<L, P> copiedNet = copyNetAndUpdateData(petriNet);
		final SynthesizeLockRule<L, P> rule = new SynthesizeLockRule<>(mStatistics, copiedNet, mCoEnabledRelation,
				mIndependenceCache, mMoverCheck, mPlaceFactory, true);
		rule.apply();

		return copiedNet;
	}

	/**
	 * @deprecated This wrapper is only supposed to exist temporarily
	 */
	@Deprecated(since = "2021-09-14")
	private BoundedPetriNet<L, P> choiceRuleWrapper(final BoundedPetriNet<L, P> petriNet) {
		final BoundedPetriNet<L, P> copiedNet = copyNetAndUpdateData(petriNet);
		final ChoiceRule<L, P> rule =
				new ChoiceRule<>(mStatistics, copiedNet, mCoEnabledRelation, mCompositionFactory, mIndependenceCache);
		rule.apply();

		mChoiceCompositions.putAll(rule.getCompositions());
		return copiedNet;
	}

	/**
	 * @deprecated Only needed for wrappers, should be removed in the future
	 */
	@Deprecated(since = "2021-09-14")
	private BoundedPetriNet<L, P> copyNetAndUpdateData(final BoundedPetriNet<L, P> petriNet) {
		final Map<ITransition<L, P>, ITransition<L, P>> oldToNewTransitions = new HashMap<>();
		final BoundedPetriNet<L, P> copiedNet = CopySubnet.copy(mServices, petriNet,
				new HashSet<>(petriNet.getTransitions()), petriNet.getAlphabet(), true, oldToNewTransitions);
		oldToNewTransitions.forEach((oldT, newT) -> mNewToOldTransitions.put(newT, getOriginalTransition(oldT)));
		oldToNewTransitions.forEach(mCoEnabledRelation::replaceElement);
		return copiedNet;
	}

	/**
	 * Check whether the first transition needs to be kept after composing two transitions.
	 *
	 * @param place
	 *            The place where the compositions happens at.
	 * @param t1
	 *            The first transition.
	 * @param t2
	 *            The second transition.
	 * @param petriNet
	 *            The Petri net.
	 * @return true if the first transition is still needed after compossition, false if the transition can be deleted.
	 */
	private boolean isFirstTransitionNeeded(final P place, final ITransition<L, P> t1, final ITransition<L, P> t2,
			final BoundedPetriNet<L, P> petriNet) {
		if (!mStuckPlaceChecker.mightGetStuck(petriNet, place)) {
			return false;
		}

		// Check whether any transition which either
		// - is co-enabled to t1 or t2, or
		// - is a successor of a successor place of t1 other than the given place
		// is an ancestor of an accepting place.
		final Set<ITransition<L, P>> relevantTransitions = new HashSet<>(mCoEnabledRelation.getImage(t1));
		relevantTransitions.addAll(mCoEnabledRelation.getImage(t2));
		petriNet.getSuccessors(t1).stream().filter(p -> p != place).flatMap(p -> petriNet.getSuccessors(p).stream())
				.forEach(relevantTransitions::add);

		final Set<Event<L, P>> events =
				relevantTransitions.stream().flatMap(this::getFirstEvents).collect(Collectors.toSet());
		final Set<Event<L, P>> errorEvents =
				petriNet.getAcceptingPlaces().stream().flatMap(p -> petriNet.getPredecessors(p).stream())
						.flatMap(this::getLastEvents).collect(Collectors.toSet());

		for (final Event<L, P> errorEvent : errorEvents) {
			for (final Event<L, P> e : events) {
				if (isAncestorEvent(e, errorEvent, new HashSet<>())) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Performs the sequence rule on the Petri net.
	 *
	 * @param petriNet
	 *            The Petri net on which the sequence rule should be performed.
	 * @return new Petri net, where the sequence rule has been performed.
	 */
	private BoundedPetriNet<L, P> sequenceRule(final BoundedPetriNet<L, P> petriNet) {
		final Set<P> places = petriNet.getPlaces();
		final Set<P> initialPlaces = petriNet.getInitialPlaces();

		final Set<ITransition<L, P>> obsoleteTransitions = new HashSet<>();
		final Set<ITransition<L, P>> composedTransitions = new HashSet<>();
		final Set<Triple<L, ITransition<L, P>, ITransition<L, P>>> pendingCompositions = new HashSet<>();
		final Map<P, Set<ITransition<L, P>>> transitionsToBeReplaced = new HashMap<>();

		for (final P place : places) {
			// TODO what about accepting places?
			if (initialPlaces.contains(place)) {
				continue;
			}

			final Set<ITransition<L, P>> incomingTransitions = petriNet.getPredecessors(place);
			final Set<ITransition<L, P>> outgoingTransitions = petriNet.getSuccessors(place);

			if (incomingTransitions.isEmpty() || outgoingTransitions.isEmpty()) {
				continue;
			}

			if (incomingTransitions.size() != 1 && outgoingTransitions.size() != 1) {
				// At the moment we only allow n:1 or 1:m compositions; because for n:m compositions,
				// (1) the number of transitions increases (n*m instead of n+m), and
				// (2) more importantly, it is unclear how to proceed if not all pairs can be composed.
				//
				// Possible future extension: If some incoming (resp. outgoing) transition t can be composed with all
				// outgoing (resp. incoming) transitions, we can perform these compositions and remove transition t.
				//
				// Alternatively, we could allow all n:m compositions and redirect the remaining uncomposed transitions
				// to several different copies of the current place.
				continue;
			}
			final boolean isYv = incomingTransitions.size() != 1;

			final Set<ITransition<L, P>> composedHere = new HashSet<>();
			boolean completeComposition = true;

			final Set<ITransition<L, P>> replacementNeeded = new HashSet<>();

			for (final ITransition<L, P> t1 : incomingTransitions) {
				if (composedTransitions.contains(t1) || petriNet.getPredecessors(t1).contains(place)) {
					completeComposition = false;
					continue;
				}

				for (final ITransition<L, P> t2 : outgoingTransitions) {
					final boolean canCompose =
							!composedTransitions.contains(t2) && sequenceRuleCheck(t1, t2, place, petriNet);
					completeComposition = completeComposition && canCompose;
					if (!canCompose) {
						continue;
					}

					if (canFireSequenceInOneSafeNet(petriNet, t1, t2)) {
						final L composedLetter = mCompositionFactory.composeSequential(t1.getSymbol(), t2.getSymbol());
						mLogger.debug("Composing " + t1 + " and " + t2);
						pendingCompositions.add(new Triple<>(composedLetter, t1, t2));
					} else {
						// This means the transitions t1.t2 can never be fired in direct sequence in a one-safe net:
						// Either some place would need to have 2 tokens, or some place would receive 2 tokens.
						//
						// TODO What is the best course of action here?
						// TODO As-is, the subsequent modifications (composedHere, replacementNeeded, statistics,
						// obsoleteTransitions) seem dangerous.
						mLogger.debug("Discarding composition of " + t1 + " and " + t2 + ".");
					}
					composedHere.add(t1);
					composedHere.add(t2);

					if (!replacementNeeded.contains(t1) && isFirstTransitionNeeded(place, t1, t2, petriNet)) {
						// TODO add setting to forbid compositions where t1 must be replaced
						replacementNeeded.add(t1);
					}

					// t1 (in an n:1 composition) resp. t2 (in a 1:m composition) is definitely obsolete.
					obsoleteTransitions.add(isYv ? t1 : t2);

					LiptonReductionStatisticsDefinitions stat;
					if (mCoEnabledRelation.getImage(t1).isEmpty() && mCoEnabledRelation.getImage(t2).isEmpty()) {
						stat = isYv ? LiptonReductionStatisticsDefinitions.TrivialYvCompositions
								: LiptonReductionStatisticsDefinitions.TrivialSequentialCompositions;
					} else {
						stat = isYv ? LiptonReductionStatisticsDefinitions.ConcurrentYvCompositions
								: LiptonReductionStatisticsDefinitions.ConcurrentSequentialCompositions;
					}
					mStatistics.reportComposition(stat);
				}
			}

			if (completeComposition) {
				// If the composition is complete, the single outgoing (for n:1 compositions) resp. incoming (for 1:m
				// compositions) transition is also obsolete.
				obsoleteTransitions.addAll(isYv ? outgoingTransitions : incomingTransitions);
			}

			// TODO Why do we delay the addition to "composedTransitions" ?
			composedTransitions.addAll(composedHere);
			if (!replacementNeeded.isEmpty()) {
				transitionsToBeReplaced.put(place, replacementNeeded);
			}
		}

		for (final Map.Entry<P, Set<ITransition<L, P>>> entry : transitionsToBeReplaced.entrySet()) {
			final P deadPlace = mPlaceFactory.copyPlace(entry.getKey());
			petriNet.addPlace(deadPlace, false, false);

			// TODO Why again do we create this fresh transition rather than keeping the old one?
			for (final ITransition<L, P> t : entry.getValue()) {
				// TODO Should the transition have those other successors? Not just deadPlace?
				final Set<P> post = new HashSet<>(petriNet.getSuccessors(t));
				post.remove(entry.getKey());
				post.add(deadPlace);
				final ITransition<L, P> newTransition =
						petriNet.addTransition(t.getSymbol(), petriNet.getPredecessors(t), ImmutableSet.of(post));
				mNewToOldTransitions.put(newTransition, getOriginalTransition(t));
				mCoEnabledRelation.copyRelationships(t, newTransition);
			}
		}

		final Map<L, ITransition<L, P>> composedLetters2Transitions = new HashMap<>();
		final Map<ITransition<L, P>, ITransition<L, P>> oldToNewTransitions = new HashMap<>();
		final BoundedPetriNet<L, P> newNet = copyPetriNetWithModification(petriNet, pendingCompositions,
				obsoleteTransitions, composedLetters2Transitions, oldToNewTransitions);

		// update information for composed transition
		for (final Triple<L, ITransition<L, P>, ITransition<L, P>> composition : pendingCompositions) {
			final ITransition<L, P> composedTransition = composedLetters2Transitions.get(composition.getFirst());
			mCoEnabledRelation.copyRelationships(composition.getSecond(), composedTransition);
			updateSequentialCompositions(composedTransition, composition.getSecond(), composition.getThird());
			transferMoverProperties(composition.getFirst(), composition.getSecond().getSymbol(),
					composition.getThird().getSymbol());
		}

		// delete obsolete information
		for (final ITransition<L, P> t : obsoleteTransitions) {
			mCoEnabledRelation.deleteElement(t);
		}

		oldToNewTransitions.forEach(mCoEnabledRelation::replaceElement);
		return newNet;
	}

	/**
	 * Checks a necessary condition for the two transitions being fireable in direct sequence in a one-safe Petri net.
	 * Specifically, checks if this firing sequence would either require some place to have two tokens, or would deposit
	 * two tokens in some place.
	 */
	private static <L, P> boolean canFireSequenceInOneSafeNet(final BoundedPetriNet<L, P> petriNet,
			final ITransition<L, P> first, final ITransition<L, P> second) {
		final Set<P> firstSucc = petriNet.getSuccessors(first);
		final Set<P> secondPre = petriNet.getPredecessors(second);

		return DataStructureUtils.intersectionStream(petriNet.getPredecessors(first), secondPre)
				.allMatch(firstSucc::contains)
				&& DataStructureUtils.intersectionStream(firstSucc, petriNet.getSuccessors(second))
						.allMatch(secondPre::contains);
	}

	/**
	 * Updates the mSequentialCompositions. This is needed for the backtranslation.
	 *
	 * @param composedLetter
	 *            The sequentially composed letter.
	 * @param transition1
	 *            The first transition that has been sequentially composed.
	 * @param transition2
	 *            The second transition that has been sequentially composed.
	 */
	private void updateSequentialCompositions(final ITransition<L, P> composed, final ITransition<L, P> transition1,
			final ITransition<L, P> transition2) {
		mSequentialCompositions.put(composed, List.of(transition1, transition2));
	}

	/**
	 * Checks whether the sequence Rule can be performed.
	 *
	 * @param t1
	 *            The first transition that might be sequentially composed.
	 * @param t2
	 *            The second transition that might be sequentially composed.
	 * @param place
	 *            The place connecting t1 and t2.
	 * @param petriNet
	 *            The Petri Net.
	 * @return true iff the sequence rule can be performed.
	 */
	private boolean sequenceRuleCheck(final ITransition<L, P> t1, final ITransition<L, P> t2, final P place,
			final BoundedPetriNet<L, P> petriNet) {
		final boolean composable = mCompositionFactory.isSequentiallyComposable(t1.getSymbol(), t2.getSymbol());
		if (!composable) {
			return false;
		}

		final boolean structurallyCorrect =
				!petriNet.getSuccessors(t2).contains(place) && checkForEventsInBetween(t1, t2, place, petriNet);
		if (!structurallyCorrect) {
			return false;
		}
		return performMoverCheck(petriNet, t1, t2);
	}

	private Stream<ITransition<L, P>> getFirstTransitions(final ITransition<L, P> t) {
		if (mSequentialCompositions.containsKey(t)) {
			final List<ITransition<L, P>> transitions = mSequentialCompositions.get(t);
			return getFirstTransitions(transitions.get(0));
		} else if (mChoiceCompositions.containsKey(t)) {
			return mChoiceCompositions.get(t).stream().flatMap(this::getFirstTransitions);
		} else {
			final ITransition<L, P> original = getOriginalTransition(t);
			if (original == t) {
				assert !mSequentialCompositions.containsKey(original) && !mChoiceCompositions.containsKey(original);
				return Stream.of(original);
			}
			return getFirstTransitions(original);
		}
	}

	private Stream<ITransition<L, P>> getLastTransitions(final ITransition<L, P> t) {
		if (mSequentialCompositions.containsKey(t)) {
			final List<ITransition<L, P>> transitions = mSequentialCompositions.get(t);
			return getLastTransitions(transitions.get(transitions.size() - 1));
		} else if (mChoiceCompositions.containsKey(t)) {
			return mChoiceCompositions.get(t).stream().flatMap(this::getLastTransitions);
		} else {
			final ITransition<L, P> original = getOriginalTransition(t);
			if (original == t) {
				assert !mSequentialCompositions.containsKey(original) && !mChoiceCompositions.containsKey(original);
				return Stream.of(original);
			}
			return getLastTransitions(original);
		}
	}

	private Stream<Event<L, P>> getFirstEvents(final ITransition<L, P> t) {
		return getFirstTransitions(t).flatMap(t2 -> mBranchingProcess.getEvents(t2).stream());
	}

	private Stream<Event<L, P>> getLastEvents(final ITransition<L, P> t) {
		return getLastTransitions(t).flatMap(t2 -> mBranchingProcess.getEvents(t2).stream());
	}

	private boolean checkForEventsInBetween(final ITransition<L, P> t1, final ITransition<L, P> t2, final P place,
			final BoundedPetriNet<L, P> petriNet) {

		final Set<ITransition<L, P>> transitions = DataStructureUtils.difference(petriNet.getSuccessors(t1).stream()
				.flatMap(p2 -> petriNet.getSuccessors(p2).stream()).collect(Collectors.toSet()),
				petriNet.getSuccessors(place));

		final Set<Event<L, P>> t1Events =
				transitions.stream().flatMap(this::getFirstEvents).collect(Collectors.toSet());
		final Set<Event<L, P>> t2Events = getLastEvents(t2).collect(Collectors.toSet());

		for (final Event<L, P> e1 : t1Events) {
			for (final Event<L, P> e2 : t2Events) {
				if (isAncestorEvent(e1, e2, new HashSet<>())) {
					return false;
				}
			}
		}

		return true;
	}

	/**
	 * Transitions are replaced by new copies whenever the Petri net is copied during the application of a rule.
	 * Additionally, the sequence rule creates copies of the first composed transition if necessary. Given a transition
	 * of some net created during the reduction, this method returns the equivalent transition as originally used in the
	 * Petri net for which the Branching Process was calculated.
	 *
	 * However, if the given transition is the result of a composition, the same transition is returned instead.
	 *
	 * @param t
	 *            A transition
	 * @return The equivalent transition used in the original Petri net (unless the given transition is a composition)
	 */
	private ITransition<L, P> getOriginalTransition(final ITransition<L, P> t) {
		return mNewToOldTransitions.getOrDefault(t, t);
	}

	private boolean isAncestorEvent(final Event<L, P> e1, final Event<L, P> e2, final Set<Event<L, P>> cutOffsVisited) {
		if (e2.getLocalConfiguration().contains(e1)) {
			return true;
		}

		for (final Event<L, P> e3 : e2.getLocalConfiguration()) {
			if (mCutOffs.getDomain().contains(e3)) {
				for (final Event<L, P> cutoff : mCutOffs.getImage(e3)) {
					final boolean unvisited = cutOffsVisited.add(cutoff);
					if (unvisited && isAncestorEvent(e1, cutoff, cutOffsVisited)) {
						return true;
					}
				}
			}
		}

		return false;
	}

	/**
	 * Creates a new Petri Net with all the new composed edges and without any of the edges that have been composed.
	 *
	 * @param services
	 *            A {@link AutomataLibraryServices} instance.
	 * @param petriNet
	 *            The original Petri Net.
	 * @param pendingCompositions
	 *            A set that contains Triples (ab, a, b), where ab is the new letter resulting from the composition of a
	 *            and b.
	 * @return a new Petri Net with composed edges and without the edges that are not needed anymore.
	 */
	private BoundedPetriNet<L, P> copyPetriNetWithModification(final BoundedPetriNet<L, P> petriNet,
			final Set<Triple<L, ITransition<L, P>, ITransition<L, P>>> pendingCompositions,
			final Set<ITransition<L, P>> obsoleteTransitions, final Map<L, ITransition<L, P>> letters2Transitions,
			final Map<ITransition<L, P>, ITransition<L, P>> oldToNewTransitions) {

		for (final Triple<L, ITransition<L, P>, ITransition<L, P>> triplet : pendingCompositions) {
			petriNet.getAlphabet().add(triplet.getFirst());

			final Set<P> pre = new HashSet<>(petriNet.getPredecessors(triplet.getThird()));
			pre.removeAll(petriNet.getSuccessors(triplet.getSecond()));
			pre.addAll(petriNet.getPredecessors(triplet.getSecond()));

			final Set<P> post = new HashSet<>(petriNet.getSuccessors(triplet.getSecond()));
			post.removeAll(petriNet.getPredecessors(triplet.getThird()));
			post.addAll(petriNet.getSuccessors(triplet.getThird()));

			letters2Transitions.put(triplet.getFirst(),
					petriNet.addTransition(triplet.getFirst(), ImmutableSet.of(pre), ImmutableSet.of(post)));
		}

		final Set<ITransition<L, P>> transitionsToKeep = new HashSet<>(petriNet.getTransitions());
		transitionsToKeep.removeAll(obsoleteTransitions);

		final BoundedPetriNet<L, P> newPetriNet = CopySubnet.copy(mServices, petriNet, transitionsToKeep,
				petriNet.getAlphabet(), true, oldToNewTransitions);
		oldToNewTransitions.forEach((oldT, newT) -> mNewToOldTransitions.put(newT, getOriginalTransition(oldT)));
		letters2Transitions.replaceAll((l, t) -> oldToNewTransitions.get(t));
		return newPetriNet;
	}

	private boolean performMoverCheck(final BoundedPetriNet<L, P> petriNet, final ITransition<L, P> t1,
			final ITransition<L, P> t2) {
		final Set<ITransition<L, P>> coEnabled1 = mCoEnabledRelation.getImage(t1);
		final Set<ITransition<L, P>> coEnabled2 = mCoEnabledRelation.getImage(t2);

		final boolean all1 = coEnabled1.containsAll(coEnabled2);
		final boolean all2 = coEnabled2.containsAll(coEnabled1);

		return (all1 && isRightMover(petriNet, t1, coEnabled1)) || (all2 && isLeftMover(petriNet, t2, coEnabled2));
	}

	/**
	 * Checks if a Transition t1 is a left mover with regard to all its co-enabled transitions.
	 *
	 * @param petriNet
	 *            The Petri net.
	 * @param t2
	 *            A transition of the Petri Net.
	 * @param coEnabledTransitions
	 *            A set of co-enabled transitions.
	 * @return true iff t2 is left mover.
	 */
	private boolean isLeftMover(final BoundedPetriNet<L, P> petriNet, final ITransition<L, P> t2,
			final Set<ITransition<L, P>> coEnabledTransitions) {
		final Set<P> preconditions = petriNet.getPredecessors(t2);
		return coEnabledTransitions.stream()
				.allMatch(t3 -> mMoverCheck.contains(
						DataStructureUtils.union(preconditions, petriNet.getPredecessors(t3)), t3.getSymbol(),
						t2.getSymbol()));
	}

	/**
	 * Checks if a Transition is a right mover with regard to all its co-enabled transitions.
	 *
	 * @param petriNet
	 *            The Petri net.
	 * @param t1
	 *            A transition of the Petri Net.
	 * @param coEnabledTransitions
	 *            A set of co-enabled transitions.
	 * @return true iff t1 is right mover.
	 */
	private boolean isRightMover(final BoundedPetriNet<L, P> petriNet, final ITransition<L, P> t1,
			final Set<ITransition<L, P>> coEnabledTransitions) {
		final Set<P> preconditions = petriNet.getPredecessors(t1);
		return coEnabledTransitions.stream()
				.allMatch(t3 -> mMoverCheck.contains(
						DataStructureUtils.union(preconditions, petriNet.getPredecessors(t3)), t1.getSymbol(),
						t3.getSymbol()));
	}

	public BoundedPetriNet<L, P> getResult() {
		return mResult;
	}

	public Map<L, List<L>> getSequentialCompositions() {
		return mSequentialCompositions.entrySet().stream().collect(Collectors.toMap(e -> e.getKey().getSymbol(),
				e -> e.getValue().stream().map(ITransition::getSymbol).collect(Collectors.toList())));
	}

	public Map<L, Set<L>> getChoiceCompositions() {
		return mChoiceCompositions.entrySet().stream().collect(Collectors.toMap(e -> e.getKey().getSymbol(),
				e -> e.getValue().stream().map(ITransition::getSymbol).collect(Collectors.toSet())));
	}

	public LiptonReductionStatisticsGenerator getStatistics() {
		return mStatistics;
	}
}
