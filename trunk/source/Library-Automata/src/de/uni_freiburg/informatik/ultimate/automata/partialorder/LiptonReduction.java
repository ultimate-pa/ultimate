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

import java.util.ArrayDeque;
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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
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

	private static final boolean LIBERAL_ACCEPTING_TRANSITION_CHECK = true;

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
	private final Map<Transition<L, P>, Transition<L, P>> mNewToOldTransitions = new HashMap<>();

	private BoundedPetriNet<L, P> mResult;
	private final LiptonReductionStatisticsGenerator mStatistics = new LiptonReductionStatisticsGenerator();

	private final Map<Transition<L, P>, List<Transition<L, P>>> mSequentialCompositions = new HashMap<>();
	private final Map<Transition<L, P>, List<Transition<L, P>>> mChoiceCompositions = new HashMap<>();

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
					new HashSet<>(mPetriNet.getTransitions()), new HashSet<>(mPetriNet.getAlphabet()), true);

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
		final Map<Transition<L, P>, Transition<L, P>> oldToNewTransitions = new HashMap<>();
		final BoundedPetriNet<L, P> copiedNet = CopySubnet.copy(mServices, petriNet,
				new HashSet<>(petriNet.getTransitions()), petriNet.getAlphabet(), true, oldToNewTransitions);
		oldToNewTransitions.forEach((oldT, newT) -> mNewToOldTransitions.put(newT, getOriginalTransition(oldT)));
		oldToNewTransitions.forEach(mCoEnabledRelation::replaceElement);
		return copiedNet;
	}

	/**
	 * Performs the sequence rule on the Petri net.
	 *
	 * @param petriNet
	 *            The Petri net on which the sequence rule should be performed.
	 * @return new Petri net, where the sequence rule has been performed.
	 */
	private BoundedPetriNet<L, P> sequenceRule(final BoundedPetriNet<L, P> petriNet) {
		mLogger.debug("-------------------------");
		mLogger.debug("applying sequence rule...");
		mLogger.debug("-------------------------");

		final Set<Transition<L, P>> obsoleteTransitions = new HashSet<>();
		final Set<Transition<L, P>> composedTransitions = new HashSet<>();
		final Set<Triple<L, Transition<L, P>, Transition<L, P>>> pendingCompositions = new HashSet<>();
		final Map<P, Set<Transition<L, P>>> transitionsToBeReplaced = new HashMap<>();

		for (final P pivot : petriNet.getPlaces()) {
			if (!isPivotPlace(petriNet, pivot)) {
				continue;
			}

			mLogger.debug("considering pivot place %s", pivot);

			final Set<Transition<L, P>> incomingTransitions = petriNet.getPredecessors(pivot);
			final Set<Transition<L, P>> outgoingTransitions = petriNet.getSuccessors(pivot);

			// 1. cartesian product of incomingTransitions and outgoingTransitions (of type PendingComposition)
			// 2. filter out uncomposable PendingCompositions (label, structural or Lipton)
			// 3. filter out PendingCompositions involving composedTransitions
			// 4. split into executable and non-executable PendingCompositions
			// 5. determine for all incoming and outgoing transitions if they are obsolete
			// -- (i.e. all pairs involving the transition are still pending or non-executable)
			// 6. for all obsolete incoming transitions, determine if we need a copy or not
			// 7. modify the net: delete obsolete, add copies, add pending compositions

			// For transformations that are not Y-V or reverse-Y-V:
			//
			// An incoming transition t1 for which some t2 was composed is deleted, but, if
			// (a) isFirstTransitionNeeded(t1) or
			// (b) not all (t1, t2) were composed or non-executable,
			// we create a new copy p' of p, a new copy of t1 with its successor p replaced by p',
			// and for all t2 not composed (but executable) with t1,
			// we create a copy t2' with its predecessor p replaced by p'.
			//
			// For multiple t1 with the same outgoing set from their p', we can re-use the place p'.
			// Indeed, we don't even (theoretically) need to only apply this for partially composed t1;
			// for not-at-all composed t1 we have p' = p.
			// In practice, we probably want to avoid that overhead.
			//
			// For reverse-Y-V transformations, where the pivot has only one successor,
			// there might exist situations where it's better to have one p' per successor t2 (only one) rather than per
			// predecessor t1. But we might still need copies of the incoming t1 due to isFirstTransitionNeeded.

			final boolean isYv = incomingTransitions.size() != 1;

			final Set<Transition<L, P>> composedHere = new HashSet<>();
			boolean completeComposition = true;

			final Set<Transition<L, P>> replacementNeeded = new HashSet<>();

			for (final Transition<L, P> t1 : incomingTransitions) {
				if (composedTransitions.contains(t1)) {
					completeComposition = false;
					continue;
				}

				for (final Transition<L, P> t2 : outgoingTransitions) {
					if (composedTransitions.contains(t2)) {
						completeComposition = false;
						continue;
					}
					if (!isComposableAt(petriNet, t1, t2, pivot)) {
						completeComposition = false;
						continue;
					}

					if (canFireSequenceInOneSafeNet(petriNet, t1, t2)) {
						final L composedLetter = mCompositionFactory.composeSequential(t1.getSymbol(), t2.getSymbol());
						mLogger.debug("  Composing %s and %s at pivot place %s", t1, t2, pivot);
						pendingCompositions.add(new Triple<>(composedLetter, t1, t2));
					} else {
						// This means the transitions t1.t2 can never be fired in direct sequence in a one-safe net:
						// Either some place would need to have 2 tokens, or some place would receive 2 tokens.
						//
						// TODO What is the best course of action here?
						// TODO As-is, the subsequent modifications (composedHere, replacementNeeded, statistics,
						// obsoleteTransitions) seem dangerous.
						mLogger.debug("  Discarding composition of " + t1 + " and " + t2 + ".");
					}
					composedHere.add(t1);
					composedHere.add(t2);

					if (!replacementNeeded.contains(t1) && isFirstTransitionNeeded(pivot, t1, t2, petriNet)) {
						// TODO add setting to forbid compositions where t1 must be replaced
						mLogger.debug("    keeping first transition " + t1);
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
				transitionsToBeReplaced.put(pivot, replacementNeeded);
			}
		}

		for (final Map.Entry<P, Set<Transition<L, P>>> entry : transitionsToBeReplaced.entrySet()) {
			P deadNonAccepting = null;
			// P deadAccepting = null;

			for (final Transition<L, P> t : entry.getValue()) {
				P deadPlace;
				// if (hasAcceptingSuccessor(t, petriNet)) {
				// if (deadAccepting == null) {
				// deadAccepting = mPlaceFactory.copyPlace(entry.getKey());
				// petriNet.addPlace(deadAccepting, false, true);
				// }
				// deadPlace = deadAccepting;
				// } else {
				if (deadNonAccepting == null) {
					deadNonAccepting = mPlaceFactory.copyPlace(entry.getKey());
					petriNet.addPlace(deadNonAccepting, false, false);
				}
				deadPlace = deadNonAccepting;
				// }

				// TODO Should the transition have those other successors? Not just deadPlace?
				// TODO (if it just has deadPlace, then deadPlace may have to be accepting)
				final Set<P> post = new HashSet<>(t.getSuccessors());
				post.remove(entry.getKey());
				post.add(deadPlace);

				// TODO Why again do we create this fresh transition rather than keeping the old one?
				final Transition<L, P> newTransition =
						petriNet.addTransition(t.getSymbol(), t.getPredecessors(), ImmutableSet.of(post));
				mNewToOldTransitions.put(newTransition, getOriginalTransition(t));
				mCoEnabledRelation.copyRelationships(t, newTransition);
			}
		}

		final Map<L, Transition<L, P>> composedLetters2Transitions = new HashMap<>();
		final Map<Transition<L, P>, Transition<L, P>> oldToNewTransitions = new HashMap<>();
		final BoundedPetriNet<L, P> newNet = copyPetriNetWithModification(petriNet, pendingCompositions,
				obsoleteTransitions, composedLetters2Transitions, oldToNewTransitions);

		// update information for composed transition
		for (final Triple<L, Transition<L, P>, Transition<L, P>> composition : pendingCompositions) {
			final Transition<L, P> composedTransition = composedLetters2Transitions.get(composition.getFirst());
			updateCoenabledForComposition(composition.getSecond(), composition.getThird(), composedTransition);
			updateSequentialCompositions(composedTransition, composition.getSecond(), composition.getThird());
			transferMoverProperties(composition.getFirst(), composition.getSecond().getSymbol(),
					composition.getThird().getSymbol());
		}

		// delete obsolete information
		for (final Transition<L, P> t : obsoleteTransitions) {
			mCoEnabledRelation.removeElement(t);
		}

		oldToNewTransitions.forEach(mCoEnabledRelation::replaceElement);
		return newNet;
	}

	private void updateCoenabledForComposition(final Transition<L, P> t1, final Transition<L, P> t2,
			final Transition<L, P> composed) {
		for (final var t : mCoEnabledRelation.getImage(t1)) {
			if (coenabledTest(t, t1, t2)) {
				mCoEnabledRelation.addPair(composed, t);
			}
		}
	}

	// Checks a necessary condition for the transition t to be coenabled with the composition of t1 and t2.
	private boolean coenabledTest(final Transition<L, P> t, final Transition<L, P> t1, final Transition<L, P> t2) {
		assert mCoEnabledRelation.containsPair(t1, t);
		if (mCoEnabledRelation.containsPair(t2, t)) {
			return true;
		}
		return DataStructureUtils.haveNonEmptyIntersection(t.getPredecessors(), t2.getPredecessors())
				&& DataStructureUtils.intersectionStream(t.getPredecessors(), t2.getPredecessors())
						.allMatch(t1.getSuccessors()::contains);
	}

	private static final class PendingComposition<L, P> {
		private final Transition<L, P> mFirst;
		private final Transition<L, P> mSecond;

		public PendingComposition(final Transition<L, P> first, final Transition<L, P> second) {
			mFirst = first;
			mSecond = second;
		}

		public Transition<L, P> getFirst() {
			return mFirst;
		}

		public L getFirstLabel() {
			return mFirst.getSymbol();
		}

		public Transition<L, P> getSecond() {
			return mSecond;
		}

		public L getSecondLabel() {
			return mSecond.getSymbol();
		}

		public Transition<L, P> constructComposedTransition(final BoundedPetriNet<L, P> net,
				final ICompositionFactory<L> factory) {
			final var label = factory.composeSequential(getFirstLabel(), getSecondLabel());
			final var preds = DataStructureUtils.union(mFirst.getPredecessors(),
					DataStructureUtils.difference(mSecond.getPredecessors(), mFirst.getSuccessors()));
			final var succs = DataStructureUtils.union(mSecond.getSuccessors(),
					DataStructureUtils.difference(mFirst.getSuccessors(), mSecond.getPredecessors()));
			return net.addTransition(label, ImmutableSet.of(preds), ImmutableSet.of(succs));
		}

		public boolean isExecutable() {
			final Set<P> firstSucc = mFirst.getSuccessors();
			final Set<P> secondPre = mSecond.getPredecessors();

			return DataStructureUtils.intersectionStream(mFirst.getPredecessors(), secondPre)
					.allMatch(firstSucc::contains)
					&& DataStructureUtils.intersectionStream(firstSucc, mSecond.getSuccessors())
							.allMatch(secondPre::contains);
		}
	}

	/**
	 * Identifies place at which the sequence rule can be applied.
	 */
	private boolean isPivotPlace(final IPetriNet<L, P> petriNet, final P place) {
		if (petriNet.getInitialPlaces().contains(place) || petriNet.isAccepting(place)) {
			return false;
		}

		final Set<Transition<L, P>> incomingTransitions = petriNet.getPredecessors(place);
		final Set<Transition<L, P>> outgoingTransitions = petriNet.getSuccessors(place);

		if (incomingTransitions.isEmpty() || outgoingTransitions.isEmpty()) {
			return false;
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
			return false;
		}

		return true;
	}

	/**
	 * Checks a necessary condition for the two transitions being fireable in direct sequence in a one-safe Petri net.
	 * Specifically, checks if this firing sequence would either require some place to have two tokens, or would deposit
	 * two tokens in some place.
	 */
	@Deprecated
	private static <L, P> boolean canFireSequenceInOneSafeNet(final BoundedPetriNet<L, P> petriNet,
			final Transition<L, P> first, final Transition<L, P> second) {
		final Set<P> firstSucc = first.getSuccessors();
		final Set<P> secondPre = second.getPredecessors();

		return DataStructureUtils.intersectionStream(first.getPredecessors(), secondPre).allMatch(firstSucc::contains)
				&& DataStructureUtils.intersectionStream(firstSucc, second.getSuccessors())
						.allMatch(secondPre::contains);
	}

	/**
	 * Check whether the first transition needs to be kept after composing two transitions.
	 *
	 * @param pivot
	 *            The place where the compositions happens at.
	 * @param t1
	 *            The first transition.
	 * @param t2
	 *            The second transition.
	 * @param petriNet
	 *            The Petri net.
	 * @return true if the first transition is still needed after composition, false if the transition can be deleted.
	 */
	private boolean isFirstTransitionNeeded(final P pivot, final Transition<L, P> t1, final Transition<L, P> t2,
			final IPetriNet<L, P> petriNet) {
		if (hasAcceptingSuccessor(t1, petriNet)) {
			// If any successor of t1 is accepting, we need to preserve t1.
			mLogger.debug("  first transition %s is needed because it has accepting successors", t1);
			return true;
		}

		if (!mStuckPlaceChecker.mightGetStuck(petriNet, pivot)) {
			mLogger.debug("  first transition %s is NOT needed because pivot place %s cannot get stuck", t1, pivot);
			return false;
		}

		if (LIBERAL_ACCEPTING_TRANSITION_CHECK) {
			return Stream.concat(mCoEnabledRelation.getImage(t1).stream(), mCoEnabledRelation.getImage(t2).stream())
					.distinct().anyMatch(t -> hasAcceptingSuccessor(t, petriNet));
		}

		// Check whether any transition which either
		// - is co-enabled to t1 or t2, or
		// - is a successor of a successor place of t1 other than the given place
		// is an ancestor of an accepting place.
		final Set<Transition<L, P>> relevantTransitions = new HashSet<>(mCoEnabledRelation.getImage(t1));
		relevantTransitions.addAll(mCoEnabledRelation.getImage(t2));

		// TODO Which version is correct? Or neither? Or something different? (see tests)
		// t1.getSuccessors().stream().filter(p -> p != place).flatMap(p -> petriNet.getSuccessors(p).stream())
		// .forEach(relevantTransitions::add);
		t1.getSuccessors().stream().flatMap(p -> petriNet.getSuccessors(p).stream())
				.filter(t -> !petriNet.getSuccessors(pivot).contains(t)).forEach(relevantTransitions::add);

		final Set<Event<L, P>> events =
				relevantTransitions.stream().flatMap(this::getFirstEvents).collect(Collectors.toSet());
		final Set<Event<L, P>> errorEvents =
				petriNet.getAcceptingPlaces().stream().flatMap(p -> petriNet.getPredecessors(p).stream())
						.flatMap(this::getLastEvents).collect(Collectors.toSet());

		for (final Event<L, P> errorEvent : errorEvents) {
			for (final Event<L, P> e : events) {
				if (isAncestorEvent(e, errorEvent, new HashSet<>())) {
					mLogger.debug("  first transition %s is needed because of error event %s", t1, errorEvent);
					return true;
				}
			}
		}
		return false;
	}

	private boolean hasAcceptingSuccessor(final Transition<L, P> t, final IPetriNet<L, P> petriNet) {
		return t.getSuccessors().stream().anyMatch(petriNet::isAccepting);
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
	private void updateSequentialCompositions(final Transition<L, P> composed, final Transition<L, P> transition1,
			final Transition<L, P> transition2) {
		mSequentialCompositions.put(composed, List.of(transition1, transition2));
	}

	/**
	 * Checks whether the sequence Rule can be performed.
	 *
	 * @param petriNet
	 *            The Petri Net.
	 * @param t1
	 *            The first transition that might be sequentially composed.
	 * @param t2
	 *            The second transition that might be sequentially composed.
	 * @param pivot
	 *            The place connecting t1 and t2.
	 * @return true iff the sequence rule can be performed.
	 */
	private boolean isComposableAt(final IPetriNet<L, P> petriNet, final Transition<L, P> t1, final Transition<L, P> t2,
			final P pivot) {
		return isLabelComposable(t1, t2) && isStructurallyComposableAt(petriNet, t1, t2, pivot)
				&& isLiptonComposable(t1, t2);
	}

	@Deprecated
	private boolean isLabelComposable(final Transition<L, P> t1, final Transition<L, P> t2) {
		return mCompositionFactory.isSequentiallyComposable(t1.getSymbol(), t2.getSymbol());
	}

	private boolean isStructurallyComposableAt(final IPetriNet<L, P> petriNet, final Transition<L, P> t1,
			final Transition<L, P> t2, final P pivot) {
		if (t1.getPredecessors().contains(pivot)) {
			// TODO This condition was in report but not in the code. Is it really needed?
			// TODO ^--- actually it was checked in sequenceRule() -- might make sense: it precludes ALL pairs with t1
			mLogger.debug("  cannot compose t1 = %s at pivot place %s because it loops", t1, pivot);
			return false;
		}

		if (t2.getSuccessors().contains(pivot)) {
			mLogger.debug("  cannot compose t2 = %s at pivot place %s because it loops", t2, pivot);
			return false;
		}

		if (!checkForEventsInBetween2(petriNet, t1, t2, pivot)) {
			mLogger.debug("  cannot compose %s and %s at pivot place %s because of events in between", t1, t2, pivot);
			return false;
		}
		return true;
	}

	private Stream<Transition<L, P>> getFirstTransitions(final Transition<L, P> t) {
		if (mSequentialCompositions.containsKey(t)) {
			final List<Transition<L, P>> transitions = mSequentialCompositions.get(t);
			return getFirstTransitions(transitions.get(0));
		} else if (mChoiceCompositions.containsKey(t)) {
			return mChoiceCompositions.get(t).stream().flatMap(this::getFirstTransitions);
		} else {
			final Transition<L, P> original = getOriginalTransition(t);
			if (original == t) {
				assert !mSequentialCompositions.containsKey(original) && !mChoiceCompositions.containsKey(original);
				return Stream.of(original);
			}
			return getFirstTransitions(original);
		}
	}

	private Stream<Transition<L, P>> getLastTransitions(final Transition<L, P> t) {
		if (mSequentialCompositions.containsKey(t)) {
			final List<Transition<L, P>> transitions = mSequentialCompositions.get(t);
			return getLastTransitions(transitions.get(transitions.size() - 1));
		} else if (mChoiceCompositions.containsKey(t)) {
			return mChoiceCompositions.get(t).stream().flatMap(this::getLastTransitions);
		} else {
			final Transition<L, P> original = getOriginalTransition(t);
			if (original == t) {
				assert !mSequentialCompositions.containsKey(original) && !mChoiceCompositions.containsKey(original);
				return Stream.of(original);
			}
			return getLastTransitions(original);
		}
	}

	private Stream<Event<L, P>> getFirstEvents(final Transition<L, P> t) {
		return getFirstTransitions(t).flatMap(t2 -> mBranchingProcess.getEvents(t2).stream());
	}

	private Stream<Event<L, P>> getLastEvents(final Transition<L, P> t) {
		return getLastTransitions(t).flatMap(t2 -> mBranchingProcess.getEvents(t2).stream());
	}

	private boolean checkForEventsInBetween(final IPetriNet<L, P> petriNet, final Transition<L, P> t1,
			final Transition<L, P> t2, final P pivot) {

		// TODO What precisely is the purpose of this method? can we simplify it?

		final Set<Transition<L, P>> transitions = DataStructureUtils.difference(t1.getSuccessors().stream()
				.flatMap(p2 -> petriNet.getSuccessors(p2).stream()).collect(Collectors.toSet()),
				petriNet.getSuccessors(pivot));

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

	// Candidate replacement for checkEventsInBetween.
	//
	// Performs a backwards search from events for transition t2, looking for a path to an event for t1 that contains
	// some event for a predecessor or successor transition of the pivot place (the start and target events excluded).
	//
	// The search does not have to go deep: Either an event is found immediately, or a target is reached. In either
	// case, the search terminates. However, we need special handling for cut-off events.
	//
	// The idea is that if no such path exists, then all events occurring between t1 and t2 in a firing sequence
	// must be co-related with either t1 or t2 (assuming no other predecessor or successor of the pivot place occurs).
	//
	private boolean checkForEventsInBetween2(final IPetriNet<L, P> petriNet, final Transition<L, P> t1,
			final Transition<L, P> t2, final P pivot) {
		final var targets = getFirstEvents(t1).collect(Collectors.toSet());

		final var queue = new ArrayDeque<Event<L, P>>();
		final var visited = new HashSet<Event<L, P>>();

		// TODO potential iteration order nondeterminism
		getLastEvents(t2).flatMap(e2 -> e2.getPredecessorEvents().stream()).forEach(queue::offer);

		while (!queue.isEmpty()) {
			final var ev = queue.poll();

			final var unvisited = visited.add(ev);
			if (!unvisited) {
				continue;
			}

			// Add all cut-off events to the stack that have the current event ev as companion.
			// Such cut-off events result in the same marking as the current event ev,
			// and hence can also result in the execution of an event start' for the same transition as start.
			// Since the event start' is not included in the finite prefix,
			// we simulate backwards search from start' here.
			// TODO potential iteration order nondeterminism
			queue.addAll(mCutOffs.getImage(ev));

			if (targets.stream().noneMatch(ev.getLocalConfiguration()::contains)) {
				// we are not on a path back to a target, so ignore this node
				continue;
			}

			final var trans = ev.getTransition();
			if (trans.getPredecessors().contains(pivot) || trans.getSuccessors().contains(pivot)) {
				// ignore paths through predecessors or successors of the pivot
				continue;
			}

			if (targets.contains(ev)) {
				// the path consists only of a single place, and can be ignored
				continue;
			}

			// the path contains at least event ev; so ev is between start and targets
			return false;
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
	private Transition<L, P> getOriginalTransition(final Transition<L, P> t) {
		return mNewToOldTransitions.getOrDefault(t, t);
	}

	private boolean isAncestorEvent(final Event<L, P> e1, final Event<L, P> e2, final Set<Event<L, P>> cutOffsVisited) {
		if (e2.getLocalConfiguration().contains(e1)) {
			return true;
		}

		for (final Event<L, P> e3 : e2.getLocalConfiguration()) {
			for (final Event<L, P> cutoff : mCutOffs.getImage(e3)) {
				final boolean unvisited = cutOffsVisited.add(cutoff);
				if (unvisited && isAncestorEvent(e1, cutoff, cutOffsVisited)) {
					return true;
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
			final Set<Triple<L, Transition<L, P>, Transition<L, P>>> pendingCompositions,
			final Set<Transition<L, P>> obsoleteTransitions, final Map<L, Transition<L, P>> letters2Transitions,
			final Map<Transition<L, P>, Transition<L, P>> oldToNewTransitions) {

		for (final Triple<L, Transition<L, P>, Transition<L, P>> triplet : pendingCompositions) {
			petriNet.getAlphabet().add(triplet.getFirst());

			final Set<P> pre = new HashSet<>(triplet.getThird().getPredecessors());
			pre.removeAll(triplet.getSecond().getSuccessors());
			pre.addAll(triplet.getSecond().getPredecessors());

			final Set<P> post = new HashSet<>(triplet.getSecond().getSuccessors());
			post.removeAll(triplet.getThird().getPredecessors());
			post.addAll(triplet.getThird().getSuccessors());

			letters2Transitions.put(triplet.getFirst(),
					petriNet.addTransition(triplet.getFirst(), ImmutableSet.of(pre), ImmutableSet.of(post)));
		}

		final Set<Transition<L, P>> transitionsToKeep = new HashSet<>(petriNet.getTransitions());
		transitionsToKeep.removeAll(obsoleteTransitions);

		final Set<L> newAlphabet = transitionsToKeep.stream().map(Transition::getSymbol).collect(Collectors.toSet());
		final BoundedPetriNet<L, P> newPetriNet =
				CopySubnet.copy(mServices, petriNet, transitionsToKeep, newAlphabet, true, oldToNewTransitions);
		oldToNewTransitions.forEach((oldT, newT) -> mNewToOldTransitions.put(newT, getOriginalTransition(oldT)));
		letters2Transitions.replaceAll((l, t) -> oldToNewTransitions.get(t));
		return newPetriNet;
	}

	// ************************************************* LIPTON MOVERS *************************************************

	private boolean isLiptonComposable(final Transition<L, P> t1, final Transition<L, P> t2) {
		final Set<Transition<L, P>> coEnabled1 = mCoEnabledRelation.getImage(t1);
		final Set<Transition<L, P>> coEnabled2 = mCoEnabledRelation.getImage(t2);

		final boolean all1 = coEnabled1.containsAll(coEnabled2);
		if (all1 && isRightMover(t1, coEnabled1)) {
			mLogger.debug("  %s is a right-mover and has a superset of coenabled transitions compared with %s", t1, t2);
			return true;
		}

		final boolean all2 = coEnabled2.containsAll(coEnabled1);
		if (all2 && isLeftMover(t2, coEnabled2)) {
			mLogger.debug("  %s is a left-mover and has a superset of coenabled transitions compared with %s", t1, t2);
			return true;
		}

		mLogger.debug("  %s and %s are not Lipton-composable", t1, t2);
		return false;
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
	private boolean isLeftMover(final Transition<L, P> t2, final Set<Transition<L, P>> coEnabledTransitions) {
		final Set<P> preconditions = t2.getPredecessors();
		return coEnabledTransitions.stream()
				.allMatch(t3 -> mMoverCheck.contains(DataStructureUtils.union(preconditions, t3.getPredecessors()),
						t3.getSymbol(), t2.getSymbol()));
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
	private boolean isRightMover(final Transition<L, P> t1, final Set<Transition<L, P>> coEnabledTransitions) {
		final Set<P> preconditions = t1.getPredecessors();
		return coEnabledTransitions.stream()
				.allMatch(t3 -> mMoverCheck.contains(DataStructureUtils.union(preconditions, t3.getPredecessors()),
						t1.getSymbol(), t3.getSymbol()));
	}

	// ***************************************************** OUTPUT ****************************************************

	public BoundedPetriNet<L, P> getResult() {
		return mResult;
	}

	public Map<L, List<L>> getSequentialCompositions() {
		return mSequentialCompositions.entrySet().stream().collect(Collectors.toMap(e -> e.getKey().getSymbol(),
				e -> e.getValue().stream().map(Transition::getSymbol).collect(Collectors.toList())));
	}

	public Map<L, Set<L>> getChoiceCompositions() {
		return mChoiceCompositions.entrySet().stream().collect(Collectors.toMap(e -> e.getKey().getSymbol(),
				e -> e.getValue().stream().map(Transition::getSymbol).collect(Collectors.toSet())));
	}

	public LiptonReductionStatisticsGenerator getStatistics() {
		return mStatistics;
	}
}
