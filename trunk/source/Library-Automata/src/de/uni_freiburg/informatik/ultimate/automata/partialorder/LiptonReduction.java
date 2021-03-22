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

import java.util.ArrayList;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IActionWithBranchEncoders;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
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
	protected final IIndependenceRelation<Set<P>, L> mMoverCheck;

	private BranchingProcess<L, P> mBranchingProcess;
	private final Set<Event<L, P>> mCutOffEvents;
	protected CoenabledRelation<L, P> mCoEnabledRelation;
	private final Map<L, List<ITransition<L, P>>> mSequentialCompositions = new HashMap<>();
	private final Map<L, Set<L>> mChoiceCompositions = new HashMap<>();
	private final Map<ITransition<L, P>, ITransition<L, P>> mNewToOldTransitions;

	private final BoundedPetriNet<L, P> mPetriNet;
	private BoundedPetriNet<L, P> mResult;
	protected final LiptonReductionStatisticsGenerator mStatistics = new LiptonReductionStatisticsGenerator();

	/**
	 * Performs Lipton reduction on the given Petri net.
	 *
	 * @param services
	 *            A {@link AutomataLibraryServices} instance.
	 * @param petriNet
	 *            The Petri Net on which the Lipton reduction should be performed.
	 * @param compositionFactory
	 *            An {@link ICompositionFactory} capable of performing compositions for the given alphabet.
	 * @param independenceRelation
	 *            The independence relation used for mover checks.
	 */
	public LiptonReduction(final AutomataLibraryServices services, final BoundedPetriNet<L, P> petriNet,
			final ICompositionFactory<L> compositionFactory,
			final IIndependenceRelation<Set<P>, L> independenceRelation) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mCompositionFactory = compositionFactory;
		mMoverCheck = independenceRelation;
		mPetriNet = petriNet;
		mCutOffEvents = new HashSet<>();
		mNewToOldTransitions = new HashMap<>();
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
			BoundedPetriNet<L, P> resultLastIteration;
			BoundedPetriNet<L, P> resultCurrentIteration = CopySubnet.copy(mServices, mPetriNet,
					new HashSet<>(mPetriNet.getTransitions()), mPetriNet.getAlphabet(), true);

			mBranchingProcess = new FinitePrefix<>(mServices, resultCurrentIteration).getResult();
			mCutOffEvents.addAll(
					mBranchingProcess.getEvents().stream().filter(Event::isCutoffEvent).collect(Collectors.toSet()));
			mCoEnabledRelation = CoenabledRelation.fromBranchingProcess(mBranchingProcess);

			final int coEnabledRelationSize = mCoEnabledRelation.size();
			mLogger.info("Number of co-enabled transitions " + coEnabledRelationSize);
			mStatistics.setCoEnabledTransitionPairs(coEnabledRelationSize);

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
		} catch (final AutomataOperationCanceledException aoce) {
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(getClass(), generateTimeoutMessage(mPetriNet));
			aoce.addRunningTaskInfo(runningTaskInfo);
			throw aoce;
		} catch (final ToolchainCanceledException tce) {
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(getClass(), generateTimeoutMessage(mPetriNet));
			tce.addRunningTaskInfo(runningTaskInfo);
			throw tce;
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
		if (mMoverCheck instanceof CachedIndependenceRelation<?, ?>) {
			((CachedIndependenceRelation<P, L>) mMoverCheck).getCache().mergeIndependencies(t1, t2, composition);
		}
	}

	private void removeMoverProperties(final L transition) {
		if (mMoverCheck instanceof CachedIndependenceRelation<?, ?>) {
			((CachedIndependenceRelation<P, L>) mMoverCheck).removeFromCache(transition);
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

				// Check if Pre- and Postset are identical for t1 and t2.
				if (petriNet.getPredecessors(t1).equals(petriNet.getPredecessors(t2))
						&& petriNet.getSuccessors(t1).equals(petriNet.getSuccessors(t2))
						&& mCompositionFactory.isParallelyComposable(Arrays.asList(t1.getSymbol(), t2.getSymbol()))
						&& checkBranchEncoders(t1.getSymbol(), t2.getSymbol())) {

					assert mCoEnabledRelation.getImage(t1).equals(mCoEnabledRelation.getImage(t2));

					// Make sure transitions not involved in any pending compositions
					if (composedTransitions.contains(t1) || composedTransitions.contains(t2)) {
						continue;
					}

					final List<L> parallelLetters = Arrays.asList(t1.getSymbol(), t2.getSymbol());
					final L composedLetter = mCompositionFactory.composeParallel(parallelLetters);
					mChoiceCompositions.put(composedLetter, new HashSet<>(parallelLetters));

					// Create new element of choiceStack.
					pendingCompositions.add(new Triple<>(composedLetter, t1, t2));
					composedTransitions.add(t1);
					composedTransitions.add(t2);

					mStatistics.reportComposition(LiptonReductionStatisticsDefinitions.ChoiceCompositions);
				}
			}
		}
		final Map<L, ITransition<L, P>> composedLetters2Transitions = new HashMap<>();
		final BoundedPetriNet<L, P> newNet = copyPetriNetWithModification(petriNet, pendingCompositions,
				composedTransitions, composedLetters2Transitions);

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
			removeMoverProperties(t.getSymbol());
		}

		return newNet;
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
		}

		final Map<L, ITransition<L, P>> composedLetters2Transitions = new HashMap<>();
		final BoundedPetriNet<L, P> newNet = copyPetriNetWithModification(petriNet, pendingCompositions,
				obsoleteTransitions, composedLetters2Transitions);

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
			removeMoverProperties(t.getSymbol());
			mSequentialCompositions.remove(t.getSymbol());
		}

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
		final List<ITransition<L, P>> combined = new ArrayList<>();

		if (mSequentialCompositions.containsKey(transition1.getSymbol())) {
			combined.addAll(mSequentialCompositions.get(transition1.getSymbol()));
		} else {
			combined.add(transition1);
		}

		if (mSequentialCompositions.containsKey(transition2.getSymbol())) {
			combined.addAll(mSequentialCompositions.get(transition2.getSymbol()));
		} else {
			combined.add(transition2);
		}

		mSequentialCompositions.put(composedLetter, combined);
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
		final boolean composable = mCompositionFactory.isComposable(t1.getSymbol(), t2.getSymbol());
		if (!composable) {
			return false;
		}

		if (!checkBranchEncoders(t1.getSymbol(), t2.getSymbol())) {
			return false;
		}

		final boolean structurallyCorrect =
				!petriNet.getSuccessors(t2).contains(place) && checkForEventsInBetween(t1, t2);
		if (!structurallyCorrect) {
			return false;
		}
		return performMoverCheck(petriNet, t1, t2);
	}

	/**
	 * Work around a problem that can happen with repeated Lipton reduction: When applying the choice rule, a formula
	 * with branch encoders is created. Then the Trace Abstraction may cause the composed transition to be duplicated
	 * with different predicates as pre- or postconditions. If we then compose the two duplicated transitions they will
	 * both have the same branch encoders and thus the resulting formula will only allow a subset of the original
	 * traces. To prevent this, we must not compose transitions with the same branch encoders.
	 *
	 * @param t1
	 *            The first letter.
	 * @param t2
	 *            The second letter.
	 * @return false if the branch encoders prevent composition. true otherwise.
	 */
	private boolean checkBranchEncoders(final L t1, final L t2) {
		return !(t1 instanceof IActionWithBranchEncoders && t2 instanceof IActionWithBranchEncoders
				&& DataStructureUtils.haveNonEmptyIntersection(
						((IActionWithBranchEncoders) t1).getTransitionFormulaWithBranchEncoders().getBranchEncoders(),
						((IActionWithBranchEncoders) t2).getTransitionFormulaWithBranchEncoders().getBranchEncoders()));
	}

	private boolean checkForEventsInBetween(final ITransition<L, P> t1, final ITransition<L, P> t2) {
		final Set<Event<L, P>> ignoredEvents = new HashSet<>();

		final Set<Event<L, P>> t1Events;
		if (mSequentialCompositions.containsKey(t1.getSymbol())) {
			final List<ITransition<L, P>> originalTransitions = mSequentialCompositions.get(t1.getSymbol());
			final ITransition<L, P> relevantTransition = originalTransitions.get(0);
			t1Events = mBranchingProcess.getEvents(getOriginalTransition(relevantTransition));
			ignoredEvents.addAll(originalTransitions.stream().flatMap(t -> mBranchingProcess.getEvents(t).stream())
					.collect(Collectors.toList()));
		} else if (mChoiceCompositions.containsKey(t1.getSymbol())) {
			// Skip this case for now
			return false;
		} else {
			t1Events = mBranchingProcess.getEvents(getOriginalTransition(t1));
			ignoredEvents.addAll(t1Events);
		}

		final Set<Event<L, P>> t2Events;
		if (mSequentialCompositions.containsKey(t2.getSymbol())) {
			final List<ITransition<L, P>> originalTransitions = mSequentialCompositions.get(t2.getSymbol());
			final ITransition<L, P> relevantTransition = originalTransitions.get(originalTransitions.size() - 1);
			t2Events = mBranchingProcess.getEvents(getOriginalTransition(relevantTransition));
			ignoredEvents.addAll(originalTransitions.stream().flatMap(t -> mBranchingProcess.getEvents(t).stream())
					.collect(Collectors.toList()));
		} else if (mChoiceCompositions.containsKey(t2.getSymbol())) {
			// Skip this case for now
			return false;
		} else {
			t2Events = mBranchingProcess.getEvents(getOriginalTransition(t2));
			ignoredEvents.addAll(t2Events);
		}

		assert !t1Events.isEmpty();
		assert !t2Events.isEmpty();

		for (final Event<L, P> e1 : t1Events) {
			for (final Event<L, P> e2 : t2Events) {
				if (containsEventInBetween(e1, e2, ignoredEvents)) {
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

	private boolean containsEventInBetween(final Event<L, P> e1, final Event<L, P> e2,
			final Set<Event<L, P>> ignoredEvents) {
		for (final Event<L, P> e3 : e2.getLocalConfiguration()) {
			if (ignoredEvents.contains(e3)) {
				continue;
			}
			if (e3.getLocalConfiguration().contains(e1)) {
				return true;
			}
		}

		// Check cutoff events.
		for (final Event<L, P> e3 : mCutOffEvents) {
			final Event<L, P> companion = e3.getCompanion();
			if (ignoredEvents.contains(e3)) {
				continue;
			}
			if (e2.getLocalConfiguration().contains(companion) && e3.getLocalConfiguration().contains(e1)) {
				return true;
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
			final Set<ITransition<L, P>> obsoleteTransitions, final Map<L, ITransition<L, P>> letters2Transitions) {

		for (final Triple<L, ITransition<L, P>, ITransition<L, P>> triplet : pendingCompositions) {
			petriNet.getAlphabet().add(triplet.getFirst());

			final Set<P> pre = new HashSet<>(petriNet.getPredecessors(triplet.getThird()));
			pre.removeAll(petriNet.getSuccessors(triplet.getSecond()));
			pre.addAll(petriNet.getPredecessors(triplet.getSecond()));

			final Set<P> post = new HashSet<>(petriNet.getSuccessors(triplet.getSecond()));
			post.removeAll(petriNet.getPredecessors(triplet.getThird()));
			post.addAll(petriNet.getSuccessors(triplet.getThird()));

			letters2Transitions.put(triplet.getFirst(), petriNet.addTransition(triplet.getFirst(), pre, post));
		}

		final Set<ITransition<L, P>> transitionsToKeep = new HashSet<>(petriNet.getTransitions());
		transitionsToKeep.removeAll(obsoleteTransitions);

		final Map<ITransition<L, P>, ITransition<L, P>> oldToNewTransitions = new HashMap<>();
		final BoundedPetriNet<L, P> newPetriNet = CopySubnet.copy(mServices, petriNet, transitionsToKeep,
				petriNet.getAlphabet(), true, oldToNewTransitions);
		oldToNewTransitions.forEach(mCoEnabledRelation::replaceElement);
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

		if (all1 && !all2) {
			return isRightMover(petriNet, t1, coEnabled1);
		} else if (!all1 && all2) {
			return isLeftMover(petriNet, t2, coEnabled2);
		} else if (all1) {
			return isRightMover(petriNet, t1, coEnabled1) || isLeftMover(petriNet, t2, coEnabled2);
		} else {
			return false;
		}
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
		return mChoiceCompositions;
	}

	public LiptonReductionStatisticsGenerator getStatistics() {
		return mStatistics;
	}
}
