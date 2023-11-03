/*
 * Copyright (C) 2019 Elisabeth Schanno
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.CopySubnet;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
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
	private final IIndependenceRelation<?, L> mMoverCheck;

	private final CoenabledRelation<L> mCoEnabledRelation;
	private final Map<L, List<L>> mSequentialCompositions = new HashMap<>();
	private final Map<L, Set<L>> mChoiceCompositions = new HashMap<>();

	private final BoundedPetriNet<L, P> mResult;
	private final LiptonReductionStatisticsGenerator mStatistics = new LiptonReductionStatisticsGenerator();

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
	 *
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled.
	 * @throws PetriNetNot1SafeException
	 *             if Petri Net is not 1-safe.
	 */
	public LiptonReduction(final AutomataLibraryServices services, final BoundedPetriNet<L, P> petriNet,
			final ICompositionFactory<L> compositionFactory, final IIndependenceRelation<?, L> independenceRelation)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mCompositionFactory = compositionFactory;
		mMoverCheck = independenceRelation;

		mStatistics.start(LiptonReductionStatisticsDefinitions.ReductionTime);
		mStatistics.collectInitialStatistics(petriNet);
		mLogger.info("Starting Lipton reduction on Petri net that " + petriNet.sizeInformation());

		try {
			mCoEnabledRelation = CoenabledRelation.fromPetriNet(mServices, petriNet);

			final int coEnabledRelationSize = mCoEnabledRelation.size();
			mLogger.info("Number of co-enabled transitions " + coEnabledRelationSize);
			mStatistics.setCoEnabledTransitionPairs(coEnabledRelationSize);

			BoundedPetriNet<L, P> resultLastIteration;
			BoundedPetriNet<L, P> resultCurrentIteration = CopySubnet.copy(services, petriNet,
					new HashSet<>(petriNet.getTransitions()), petriNet.getAlphabet(), true);
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
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(getClass(), generateTimeoutMessage(petriNet));
			aoce.addRunningTaskInfo(runningTaskInfo);
			throw aoce;
		} catch (final ToolchainCanceledException tce) {
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(getClass(), generateTimeoutMessage(petriNet));
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
		final Collection<Transition<L, P>> transitions = petriNet.getTransitions();

		final Set<Triple<L, Transition<L, P>, Transition<L, P>>> pendingCompositions = new HashSet<>();
		final Set<Transition<L, P>> composedTransitions = new HashSet<>();

		for (final Transition<L, P> t1 : transitions) {
			for (final Transition<L, P> t2 : transitions) {
				if (t1.equals(t2)) {
					continue;
				}

				// Check if Pre- and Postset are identical for t1 and t2.
				if (t1.getPredecessors().equals(t2.getPredecessors()) && t1.getSuccessors().equals(t2.getSuccessors())
						&& mCompositionFactory.isComposable(t1.getSymbol())
						&& mCompositionFactory.isComposable(t2.getSymbol())) {

					assert mCoEnabledRelation.getImage(t1.getSymbol())
							.equals(mCoEnabledRelation.getImage(t2.getSymbol()));

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
		final BoundedPetriNet<L, P> newNet =
				copyPetriNetWithModification(petriNet, pendingCompositions, composedTransitions);

		// update information for composed transition
		for (final Triple<L, Transition<L, P>, Transition<L, P>> composition : pendingCompositions) {
			mCoEnabledRelation.copyRelationships(composition.getSecond().getSymbol(), composition.getFirst());
			transferMoverProperties(composition.getFirst(), composition.getSecond().getSymbol(),
					composition.getThird().getSymbol());
		}

		// delete obsolete information
		for (final Transition<L, P> t : composedTransitions) {
			mCoEnabledRelation.deleteElement(t.getSymbol());
			removeMoverProperties(t.getSymbol());
		}

		return newNet;
	}

	/**
	 * Performs the sequence rule on the Petri net.
	 *
	 * @param services
	 *            A {@link AutomataLibraryServices} instance.
	 * @param petriNet
	 *            The Petri net on which the sequence rule should be performed.
	 * @return new Petri net, where the sequence rule has been performed.
	 */
	private BoundedPetriNet<L, P> sequenceRule(final BoundedPetriNet<L, P> petriNet) {
		final Collection<Transition<L, P>> transitions = petriNet.getTransitions();

		final Set<Transition<L, P>> obsoleteTransitions = new HashSet<>();
		final Set<Transition<L, P>> composedTransitions = new HashSet<>();
		final Set<Triple<L, Transition<L, P>, Transition<L, P>>> pendingCompositions = new HashSet<>();

		for (final Transition<L, P> t1 : transitions) {
			if (composedTransitions.contains(t1)) {
				continue;
			}

			final Set<P> t1PostSet = t1.getSuccessors();
			final Set<P> t1PreSet = t1.getPredecessors();

			if (t1PostSet.size() != 1) {
				// TODO: this isn't relevant for Y-V, is it?
				continue;
			}

			final P prePlace = t1PreSet.iterator().next();
			final P postPlace = t1PostSet.iterator().next();

			// Y to V check
			if (petriNet.getSuccessors(prePlace).size() == 1 && petriNet.getPredecessors(prePlace).size() > 1) {

				boolean completeComposition = true;
				boolean composed = false;

				for (final Transition<L, P> t2 : petriNet.getPredecessors(prePlace)) {
					final boolean canCompose =
							!composedTransitions.contains(t2) && sequenceRuleCheck(t2, t1, prePlace, petriNet);
					completeComposition = completeComposition && canCompose;

					if (canCompose) {
						final L composedLetter = mCompositionFactory.composeSequential(t2.getSymbol(), t1.getSymbol());

						// create new element of the sequentialCompositionStack.
						pendingCompositions.add(new Triple<>(composedLetter, t2, t1));
						composedTransitions.add(t1);
						composedTransitions.add(t2);
						obsoleteTransitions.add(t2);
						composed = true;

						if (mCoEnabledRelation.getImage(t1.getSymbol()).isEmpty()) {
							mStatistics.reportComposition(LiptonReductionStatisticsDefinitions.TrivialYvCompositions);
						} else {
							mStatistics
									.reportComposition(LiptonReductionStatisticsDefinitions.ConcurrentYvCompositions);
						}
					}
				}
				if (completeComposition && composed) {
					obsoleteTransitions.add(t1);
				}

			} else if (petriNet.getPredecessors(postPlace).size() == 1) {

				boolean completeComposition = true;
				boolean composed = false;

				for (final Transition<L, P> t2 : petriNet.getSuccessors(postPlace)) {
					final boolean canCompose =
							!composedTransitions.contains(t2) && sequenceRuleCheck(t1, t2, postPlace, petriNet);
					completeComposition = completeComposition && canCompose;

					if (canCompose) {
						final L composedLetter = mCompositionFactory.composeSequential(t1.getSymbol(), t2.getSymbol());

						// create new element of the sequentialCompositionStack.
						pendingCompositions.add(new Triple<>(composedLetter, t1, t2));
						composedTransitions.add(t1);
						composedTransitions.add(t2);
						obsoleteTransitions.add(t2);
						composed = true;

						if (mCoEnabledRelation.getImage(t1.getSymbol()).isEmpty()) {
							mStatistics.reportComposition(
									LiptonReductionStatisticsDefinitions.TrivialSequentialCompositions);
						} else {
							mStatistics.reportComposition(
									LiptonReductionStatisticsDefinitions.ConcurrentSequentialCompositions);
						}
					}
				}
				if (completeComposition && composed) {
					obsoleteTransitions.add(t1);
				}
			}

		}
		final BoundedPetriNet<L, P> newNet =
				copyPetriNetWithModification(petriNet, pendingCompositions, obsoleteTransitions);

		// update information for composed transition
		for (final Triple<L, Transition<L, P>, Transition<L, P>> composition : pendingCompositions) {
			mCoEnabledRelation.copyRelationships(composition.getSecond().getSymbol(), composition.getFirst());
			updateSequentialCompositions(composition.getFirst(), composition.getSecond().getSymbol(),
					composition.getThird().getSymbol());
			transferMoverProperties(composition.getFirst(), composition.getSecond().getSymbol(),
					composition.getThird().getSymbol());
		}

		// delete obsolete information
		for (final Transition<L, P> t : obsoleteTransitions) {
			mCoEnabledRelation.deleteElement(t.getSymbol());
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
	 * @param letter1
	 *            The first letter that has been sequentially composed.
	 * @param letter2
	 *            The second letter that has been sequentially composed.
	 */
	private void updateSequentialCompositions(final L composedLetter, final L letter1, final L letter2) {
		final List<L> combined = new ArrayList<>();

		if (mSequentialCompositions.containsKey(letter1)) {
			combined.addAll(mSequentialCompositions.get(letter1));
		} else {
			combined.add(letter1);
		}

		if (mSequentialCompositions.containsKey(letter2)) {
			combined.addAll(mSequentialCompositions.get(letter2));
		} else {
			combined.add(letter2);
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
	private boolean sequenceRuleCheck(final Transition<L, P> t1, final Transition<L, P> t2, final P place,
			final BoundedPetriNet<L, P> petriNet) {

		final boolean composable =
				mCompositionFactory.isComposable(t1.getSymbol()) && mCompositionFactory.isComposable(t2.getSymbol());
		final boolean structurallyCorrect = t2.getPredecessors().size() == 1 && !t2.getSuccessors().contains(place);
		final boolean moverProperties = isRightMover(t1) || isLeftMover(t2);

		return composable && structurallyCorrect && moverProperties;
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
			final Set<Transition<L, P>> obsoleteTransitions) {

		for (final Triple<L, Transition<L, P>, Transition<L, P>> triplet : pendingCompositions) {
			petriNet.getAlphabet().add(triplet.getFirst());
			petriNet.addTransition(triplet.getFirst(), triplet.getSecond().getPredecessors(),
					triplet.getThird().getSuccessors());
		}

		final Set<Transition<L, P>> transitionsToKeep = new HashSet<>(petriNet.getTransitions());
		transitionsToKeep.removeAll(obsoleteTransitions);

		// Create new net
		return CopySubnet.copy(mServices, petriNet, transitionsToKeep, petriNet.getAlphabet(), true);
	}

	/**
	 * Checks if a Transition t1 is a left mover with regard to all its co-enabled transitions.
	 *
	 * @param t1
	 *            A transition of the Petri Net.
	 * @return true iff t1 is left mover.
	 */
	private boolean isLeftMover(final Transition<L, P> t1) {
		final Set<L> coEnabledTransitions = mCoEnabledRelation.getImage(t1.getSymbol());
		mStatistics.reportMoverChecks(coEnabledTransitions.size());
		return coEnabledTransitions.stream()
				.allMatch(t2 -> mMoverCheck.isIndependent(null, t2, t1.getSymbol()) == Dependence.INDEPENDENT);
	}

	/**
	 * Checks if a Transition is a right mover with regard to all its co-enabled transitions.
	 *
	 * @param t1
	 *            A transition of the Petri Net.
	 * @return true iff t1 is right mover.
	 */
	private boolean isRightMover(final Transition<L, P> t1) {
		final Set<L> coEnabledTransitions = mCoEnabledRelation.getImage(t1.getSymbol());
		mStatistics.reportMoverChecks(coEnabledTransitions.size());
		return coEnabledTransitions.stream()
				.allMatch(t2 -> mMoverCheck.isIndependent(null, t1.getSymbol(), t2) == Dependence.INDEPENDENT);
	}

	public BoundedPetriNet<L, P> getResult() {
		return mResult;
	}

	public Map<L, List<L>> getSequentialCompositions() {
		return mSequentialCompositions;
	}

	public Map<L, Set<L>> getChoiceCompositions() {
		return mChoiceCompositions;
	}

	public LiptonReductionStatisticsGenerator getStatistics() {
		return mStatistics;
	}
}
