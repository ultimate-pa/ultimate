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

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
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
	private final Map<L, List<ITransition<L, P>>> mSequentialCompositions = new HashMap<>();
	private final Map<L, Set<ITransition<L, P>>> mChoiceCompositions = new HashMap<>();

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
		mLogger = services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
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

				resultCurrentIteration = sequenceRule(resultLastIteration);
				resultCurrentIteration = choiceRule(resultCurrentIteration);
			} while (resultLastIteration.getTransitions().size() != resultCurrentIteration.getTransitions().size());
			mResult = resultCurrentIteration;

			mLogger.info("Checked pairs total: "
					+ mStatistics.getValue(LiptonReductionStatisticsDefinitions.MoverChecksTotal));
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
	 * Performs the choice rule on a Petri net.
	 *
	 * @param services
	 *            A {@link AutomataLibraryServices} instance.
	 * @param petriNet
	 *            The Petri net on which the choice rule should be performed.
	 * @return new Petri net, where the choice rule has been performed.
	 */
	private BoundedPetriNet<L, P> choiceRule(final BoundedPetriNet<L, P> petriNet) {
		final Collection<ITransition<L, P>> transitions = petriNet.getTransitions();

		final Set<Triple<L, ITransition<L, P>, ITransition<L, P>>> pendingCompositions = new HashSet<>();
		final Set<ITransition<L, P>> composedTransitions = new HashSet<>();

		for (final ITransition<L, P> t1 : transitions) {
			for (final ITransition<L, P> t2 : transitions) {
				if (t1.equals(t2)) {
					continue;
				}

				// Make sure transitions not involved in any pending compositions
				if (composedTransitions.contains(t1) || composedTransitions.contains(t2)) {
					continue;
				}

				// Check if Pre- and Postset are identical for t1 and t2.
				if (petriNet.getPredecessors(t1).equals(petriNet.getPredecessors(t2))
						&& petriNet.getSuccessors(t1).equals(petriNet.getSuccessors(t2))
						&& mCompositionFactory.isParallelyComposable(Arrays.asList(t1.getSymbol(), t2.getSymbol()))) {

					assert mCoEnabledRelation.getImage(t1).equals(mCoEnabledRelation.getImage(t2));

					final List<L> parallelLetters = Arrays.asList(t1.getSymbol(), t2.getSymbol());
					final L composedLetter = mCompositionFactory.composeParallel(parallelLetters);
					mChoiceCompositions.put(composedLetter, Set.of(t1, t2));

					// Create new element of pendingCompositions.
					pendingCompositions.add(new Triple<>(composedLetter, t1, t2));
					composedTransitions.add(t1);
					composedTransitions.add(t2);

					mStatistics.reportComposition(LiptonReductionStatisticsDefinitions.ChoiceCompositions);
				}
			}
		}
		final Map<L, ITransition<L, P>> composedLetters2Transitions = new HashMap<>();
		final Map<ITransition<L, P>, ITransition<L, P>> oldToNewTransitions = new HashMap<>();
		final BoundedPetriNet<L, P> newNet = copyPetriNetWithModification(petriNet, pendingCompositions,
				composedTransitions, composedLetters2Transitions, oldToNewTransitions);

		// update information for composed transition
		for (final Triple<L, ITransition<L, P>, ITransition<L, P>> composition : pendingCompositions) {
			mCoEnabledRelation.copyRelationships(composition.getSecond(),
					composedLetters2Transitions.get(composition.getFirst()));
			transferMoverProperties(composition.getFirst(), composition.getSecond().getSymbol(),
					composition.getThird().getSymbol());
		}

		// delete obsolete information
		for (final ITransition<L, P> t : composedTransitions) {
			mCoEnabledRelation.deleteElement(t);
		}

		oldToNewTransitions.forEach(mCoEnabledRelation::replaceElement);
		return newNet;
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
				relevantTransitions.stream().flatMap(t -> getFirstEvents(t).stream()).collect(Collectors.toSet());
		final Set<Event<L, P>> errorEvents =
				petriNet.getAcceptingPlaces().stream().flatMap(p -> petriNet.getPredecessors(p).stream())
						.flatMap(t -> getLastEvents(t).stream()).collect(Collectors.toSet());

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
			if (initialPlaces.contains(place)) {
				continue;
			}

			final Set<ITransition<L, P>> incomingTransitions = petriNet.getPredecessors(place);
			final Set<ITransition<L, P>> outgoingTransitions = petriNet.getSuccessors(place);

			if (incomingTransitions.isEmpty() || outgoingTransitions.isEmpty()) {
				continue;
			}

			if (incomingTransitions.size() != 1 && outgoingTransitions.size() != 1) {
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

					if (canCompose) {
						final Set<P> pre2 = new HashSet<>(petriNet.getPredecessors(t2));
						pre2.removeAll(petriNet.getSuccessors(t1));
						final Set<P> post1 = new HashSet<>(petriNet.getSuccessors(t1));
						post1.removeAll(petriNet.getPredecessors(t2));

						if (Collections.disjoint(petriNet.getPredecessors(t1), pre2)
								&& Collections.disjoint(petriNet.getSuccessors(t2), post1)) {
							final L composedLetter =
									mCompositionFactory.composeSequential(t1.getSymbol(), t2.getSymbol());
							mLogger.debug("Composing " + t1 + " and " + t2);
							pendingCompositions.add(new Triple<>(composedLetter, t1, t2));
						} else {
							mLogger.debug("Discarding composition of " + t1 + " and " + t2 + ".");
						}
						composedHere.add(t1);
						composedHere.add(t2);

						if (isFirstTransitionNeeded(place, t1, t2, petriNet)) {
							replacementNeeded.add(t1);
						}

						if (isYv) {
							obsoleteTransitions.add(t1);
						} else {
							obsoleteTransitions.add(t2);
						}

						LiptonReductionStatisticsDefinitions stat;
						if (mCoEnabledRelation.getImage(t1).isEmpty()) {
							stat = isYv ? LiptonReductionStatisticsDefinitions.TrivialYvCompositions
									: LiptonReductionStatisticsDefinitions.TrivialSequentialCompositions;
						} else {
							stat = isYv ? LiptonReductionStatisticsDefinitions.ConcurrentYvCompositions
									: LiptonReductionStatisticsDefinitions.ConcurrentSequentialCompositions;
						}
						mStatistics.reportComposition(stat);
					}
				}
			}

			if (completeComposition) {
				if (isYv) {
					obsoleteTransitions.addAll(outgoingTransitions);
				} else {
					obsoleteTransitions.addAll(incomingTransitions);
				}
			}

			composedTransitions.addAll(composedHere);
			if (!replacementNeeded.isEmpty()) {
				transitionsToBeReplaced.put(place, replacementNeeded);
			}
		}

		for (final Map.Entry<P, Set<ITransition<L, P>>> entry : transitionsToBeReplaced.entrySet()) {
			final P deadPlace = mPlaceFactory.copyPlace(entry.getKey());
			petriNet.addPlace(deadPlace, false, false);

			for (final ITransition<L, P> t : entry.getValue()) {
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
			mCoEnabledRelation.copyRelationships(composition.getSecond(),
					composedLetters2Transitions.get(composition.getFirst()));
			updateSequentialCompositions(composition.getFirst(), composition.getSecond(), composition.getThird());
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
	 * Updates the mSequentialCompositions. This is needed for the backtranslation.
	 *
	 * @param composedLetter
	 *            The sequentially composed letter.
	 * @param transition1
	 *            The first transition that has been sequentially composed.
	 * @param transition2
	 *            The second transition that has been sequentially composed.
	 */
	private void updateSequentialCompositions(final L composedLetter, final ITransition<L, P> transition1,
			final ITransition<L, P> transition2) {
		mSequentialCompositions.put(composedLetter, List.of(transition1, transition2));
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

	private Set<ITransition<L, P>> getFirstTransitions(final ITransition<L, P> t) {
		if (mSequentialCompositions.containsKey(t.getSymbol())) {
			final List<ITransition<L, P>> transitions = mSequentialCompositions.get(t.getSymbol());
			return getFirstTransitions(transitions.get(0));
		} else if (mChoiceCompositions.containsKey(t.getSymbol())) {
			return mChoiceCompositions.get(t.getSymbol()).stream().flatMap(t2 -> getFirstTransitions(t2).stream())
					.collect(Collectors.toSet());
		} else {
			return Set.of(getOriginalTransition(t));
		}
	}

	private Set<ITransition<L, P>> getLastTransitions(final ITransition<L, P> t) {
		if (mSequentialCompositions.containsKey(t.getSymbol())) {
			final List<ITransition<L, P>> transitions = mSequentialCompositions.get(t.getSymbol());
			return getLastTransitions(transitions.get(transitions.size() - 1));
		} else if (mChoiceCompositions.containsKey(t.getSymbol())) {
			return mChoiceCompositions.get(t.getSymbol()).stream().flatMap(t2 -> getLastTransitions(t2).stream())
					.collect(Collectors.toSet());
		} else {
			return Set.of(getOriginalTransition(t));
		}
	}

	private Set<Event<L, P>> getFirstEvents(final ITransition<L, P> t) {
		return getFirstTransitions(t).stream().flatMap(t2 -> mBranchingProcess.getEvents(t2).stream())
				.collect(Collectors.toSet());
	}

	private Set<Event<L, P>> getLastEvents(final ITransition<L, P> t) {
		return getLastTransitions(t).stream().flatMap(t2 -> mBranchingProcess.getEvents(t2).stream())
				.collect(Collectors.toSet());
	}

	private boolean checkForEventsInBetween(final ITransition<L, P> t1, final ITransition<L, P> t2, final P place,
			final BoundedPetriNet<L, P> petriNet) {

		final Set<ITransition<L, P>> transitions = DataStructureUtils.difference(petriNet.getSuccessors(t1).stream()
				.flatMap(p2 -> petriNet.getSuccessors(p2).stream()).collect(Collectors.toSet()),
				petriNet.getSuccessors(place));

		final Set<Event<L, P>> t1Events =
				transitions.stream().flatMap(t -> getFirstEvents(t).stream()).collect(Collectors.toSet());
		final Set<Event<L, P>> t2Events = getLastEvents(t2);

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
	 * Returns the equivalent transition as originally used in the Petri net for which the Branching Process was
	 * calculated.
	 *
	 * @param t
	 *            A transition. The transition must not be the result of a composition.
	 * @return The equivalent transition used in the original Petri net.
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
					if (cutOffsVisited.contains(cutoff)) {
						continue;
					}
					cutOffsVisited.add(cutoff);
					if (isAncestorEvent(e1, cutoff, cutOffsVisited)) {
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
		mStatistics.reportMoverChecks(coEnabledTransitions.size());
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
		mStatistics.reportMoverChecks(coEnabledTransitions.size());
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
		return mSequentialCompositions.entrySet().stream().collect(Collectors.toMap(Map.Entry::getKey,
				e -> e.getValue().stream().map(ITransition::getSymbol).collect(Collectors.toList())));
	}

	public Map<L, Set<L>> getChoiceCompositions() {
		return mChoiceCompositions.entrySet().stream().collect(Collectors.toMap(Map.Entry::getKey,
				e -> e.getValue().stream().map(ITransition::getSymbol).collect(Collectors.toSet())));
	}

	public LiptonReductionStatisticsGenerator getStatistics() {
		return mStatistics;
	}
}
