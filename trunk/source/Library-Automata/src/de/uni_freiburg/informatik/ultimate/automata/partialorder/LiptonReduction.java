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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.CopySubnet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

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

	private final BoundedPetriNet<L, P> mPetriNet;
	private Map<PetriNetRun<L, P>, PetriNetRun<L, P>> mRuns;

	private final BranchingProcess<L, P> mBranchingProcess;
	private final ModifiableRetroMorphism<L, P> mRetromorphism;
	private final CoenabledRelation<L, P> mCoEnabledRelation;

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
	 * @param placeFactory
	 *            An {@link ICopyPlaceFactory} capable of creating places for the given Petri net.
	 * @param independenceRelation
	 *            The independence relation used for mover checks.
	 * @param stuckPlaceChecker
	 *            An {@link IPostScriptChecker}.
	 * @param finitePrefix
	 *            A complete finite prefix of the given net, if available. May be null, in which case the instance
	 *            starts its own computation of a finite prefix.
	 * @param runs
	 *            A set of accepting runs for the given Petri net. For each run in the set, the reduction will try to
	 *            find a covering run, which can be retrieved via {@link #getAdaptedRuns()}.
	 * @throws AutomataOperationCanceledException
	 * @throws PetriNetNot1SafeException
	 */
	public LiptonReduction(final AutomataLibraryServices services, final BoundedPetriNet<L, P> petriNet,
			final ICompositionFactory<L> compositionFactory, final ICopyPlaceFactory<P> placeFactory,
			final IIndependenceRelation<Set<P>, L> independenceRelation,
			final IPostScriptChecker<L, P> stuckPlaceChecker, final BranchingProcess<L, P> finitePrefix,
			final Set<PetriNetRun<L, P>> runs) throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(LiptonReduction.class);
		mCompositionFactory = compositionFactory;
		mPlaceFactory = placeFactory;
		mMoverCheck = independenceRelation;
		mStuckPlaceChecker = stuckPlaceChecker;

		// Copy the Petri net once, so the original is not modified.
		final var original2Copy = new HashMap<Transition<L, P>, Transition<L, P>>();
		mPetriNet = CopySubnet.copy(mServices, petriNet, new HashSet<>(petriNet.getTransitions()),
				new HashSet<>(petriNet.getAlphabet()), true, original2Copy);

		// Collect information used by reduction rules.
		if (finitePrefix == null) {
			mBranchingProcess = computeFinitePrefix(mPetriNet);
			// Start with the identity retromorphism.
			mRetromorphism = new ModifiableRetroMorphism<>(mPetriNet);
			// Compute the coenabled relation directly from the new branching process.
			mCoEnabledRelation = CoenabledRelation.fromBranchingProcess(mBranchingProcess);
		} else {
			mBranchingProcess = finitePrefix;

			// Build a retromorphism that maps back to transitions corresponding to the events in finitePrefix.
			mRetromorphism = new ModifiableRetroMorphism<>(petriNet);
			mRetromorphism.renameAndProjectTransitions(original2Copy);

			// Compute the coenabled relation from the given branching process, and then adapt it for the copied net.
			mCoEnabledRelation = CoenabledRelation.fromBranchingProcess(mBranchingProcess);
			mCoEnabledRelation.renameAndProjectTransitions(original2Copy);
		}
		mRuns = adaptRunsToCopy(runs, petriNet, original2Copy);

		performReduction();
	}

	private Map<PetriNetRun<L, P>, PetriNetRun<L, P>> adaptRunsToCopy(final Set<PetriNetRun<L, P>> runs,
			final IPetriNet<L, P> originalNet, final Map<Transition<L, P>, Transition<L, P>> original2Copy)
			throws PetriNetNot1SafeException {
		if (runs == null) {
			return Collections.emptyMap();
		}

		final var result = new HashMap<PetriNetRun<L, P>, PetriNetRun<L, P>>();
		for (final var run : runs) {
			assert run.isRunOf(originalNet) : "Given run does not belong to given net";

			final var adapted = adaptRunToCopy(run, original2Copy);
			assert adapted.isRunOf(mPetriNet) : "Adaptation of run to copied net failed";

			result.put(run, adapted);
		}
		return result;
	}

	private PetriNetRun<L, P> adaptRunToCopy(final PetriNetRun<L, P> run,
			final Map<Transition<L, P>, Transition<L, P>> original2Copy) {
		final var markings = IntStream.range(0, run.getLength()).mapToObj(run::getMarking).collect(Collectors.toList());
		final var transitions = IntStream.range(0, run.getLength() - 1).mapToObj(run::getTransition)
				.map(original2Copy::get).collect(Collectors.toList());
		return new PetriNetRun<>(markings, run.getWord(), transitions);
	}

	private BranchingProcess<L, P> computeFinitePrefix(final BoundedPetriNet<L, P> net)
			throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		try {
			// TODO Why call FinitePrefix and not PetriNetUnfolder directly?
			return new FinitePrefix<>(mServices, net).getResult();
		} catch (final AutomataOperationCanceledException ce) {
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(getClass(), generateTimeoutMessage(net));
			ce.addRunningTaskInfo(runningTaskInfo);
			throw ce;
		}
	}

	private void performReduction() {
		mStatistics.start(LiptonReductionStatisticsDefinitions.ReductionTime);
		mStatistics.collectInitialStatistics(mPetriNet);
		mLogger.info("Starting Lipton reduction on Petri net that " + mPetriNet.sizeInformation());

		try {
			final int coEnabledRelationSize = mCoEnabledRelation.size();
			mLogger.info("Number of co-enabled transitions " + coEnabledRelationSize);
			mStatistics.setCoEnabledTransitionPairs(coEnabledRelationSize);

			boolean changes;
			do {
				mStatistics.reportFixpointIteration();

				changes = false;

				// TODO decide on best ordering (e.g. choice at the beginning?)
				// TODO add / allow more rules, e.g. SynthesizeLockRule
				changes = sequenceRuleWrapper(mPetriNet) || changes;
				changes = choiceRuleWrapper(mPetriNet) || changes;
			} while (changes);

			mLogger.info("Total number of compositions: "
					+ mStatistics.getValue(LiptonReductionStatisticsDefinitions.TotalNumberOfCompositions));
		} finally {
			mStatistics.stop(LiptonReductionStatisticsDefinitions.ReductionTime);
		}

		mStatistics.collectFinalStatistics(mPetriNet);
	}

	private String generateTimeoutMessage(final BoundedPetriNet<L, P> petriNet) {
		if (mCoEnabledRelation == null) {
			return "applying " + getClass().getSimpleName() + " to Petri net that " + petriNet.sizeInformation();
		}
		return "applying " + getClass().getSimpleName() + " to Petri net that " + petriNet.sizeInformation() + " and "
				+ mCoEnabledRelation.size() + " co-enabled transitions pairs.";
	}

	/**
	 * @deprecated This wrapper is only supposed to exist temporarily
	 */
	@Deprecated(since = "2021-09-15")
	private boolean synthesizeLockRuleWrapper(final BoundedPetriNet<L, P> petriNet) {
		final SynthesizeLockRule<L, P> rule = new SynthesizeLockRule<>(mServices, mStatistics, petriNet,
				mCoEnabledRelation, mMoverCheck, mPlaceFactory, true, mRuns);
		final boolean result = rule.apply();
		mRuns = rule.getAdaptedRuns();
		return result;
	}

	/**
	 * @deprecated This wrapper is only supposed to exist temporarily
	 */
	@Deprecated(since = "2021-09-14")
	private boolean choiceRuleWrapper(final BoundedPetriNet<L, P> petriNet) {
		final ChoiceRule<L, P> rule = new ChoiceRule<>(mServices, mStatistics, petriNet, mCoEnabledRelation,
				mRetromorphism, mCompositionFactory, mRuns);
		final boolean result = rule.apply();
		mRuns = rule.getAdaptedRuns();
		return result;
	}

	/**
	 * @deprecated This wrapper is only supposed to exist temporarily
	 */
	@Deprecated(since = "2022-10-07")
	private boolean sequenceRuleWrapper(final BoundedPetriNet<L, P> petriNet) {
		final SequenceRule<L, P> rule =
				new SequenceRule<>(mServices, mStatistics, petriNet, mCoEnabledRelation, mRetromorphism, mMoverCheck,
						mCompositionFactory, mPlaceFactory, mStuckPlaceChecker, mBranchingProcess, mRuns);
		final boolean result = rule.apply();
		mRuns = rule.getAdaptedRuns();
		return result;
	}

	// ***************************************************** OUTPUT ****************************************************

	public BoundedPetriNet<L, P> getResult() {
		return mPetriNet;
	}

	public Map<PetriNetRun<L, P>, PetriNetRun<L, P>> getAdaptedRuns() {
		return mRuns;
	}

	public LiptonReductionStatisticsGenerator getStatistics() {
		return mStatistics;
	}
}
