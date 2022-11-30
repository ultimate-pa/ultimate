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
import java.util.Map;
import java.util.Set;

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
	private PetriNetRun<L, P> mRun;

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
	 * @throws AutomataOperationCanceledException
	 * @throws PetriNetNot1SafeException
	 */
	public LiptonReduction(final AutomataLibraryServices services, final BoundedPetriNet<L, P> petriNet,
			final ICompositionFactory<L> compositionFactory, final ICopyPlaceFactory<P> placeFactory,
			final IIndependenceRelation<Set<P>, L> independenceRelation,
			final IPostScriptChecker<L, P> stuckPlaceChecker, final BranchingProcess<L, P> finitePrefix,
			final PetriNetRun<L, P> run) throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(LiptonReduction.class);
		mCompositionFactory = compositionFactory;
		mPlaceFactory = placeFactory;
		mMoverCheck = independenceRelation;
		mStuckPlaceChecker = stuckPlaceChecker;

		mRun = run;
		if (run != null) {
			assert run.isRunOf(petriNet) : "Given run does not belong to given net";
		}

		// Copy the Petri net once, so the original is not modified.
		final var copy2Originals = new HashMap<Transition<L, P>, Transition<L, P>>();
		mPetriNet = CopySubnet.copy(mServices, petriNet, new HashSet<>(petriNet.getTransitions()),
				new HashSet<>(petriNet.getAlphabet()), true, copy2Originals);

		// Collect information used by reduction rules.
		mBranchingProcess = getFinitePrefix(finitePrefix);
		mCoEnabledRelation = CoenabledRelation.fromBranchingProcess(mBranchingProcess);
		if (finitePrefix == null) {
			mRetromorphism = new ModifiableRetroMorphism<>(mPetriNet);
		} else {
			// Build a retromorphism that maps back to transitions corresponding to the events in mBranchingProcess.
			mRetromorphism = getRetromorphism(petriNet, copy2Originals);
		}

		performReduction();
	}

	private BranchingProcess<L, P> getFinitePrefix(final BranchingProcess<L, P> finitePrefix)
			throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		if (finitePrefix != null) {
			return finitePrefix;
		}

		try {
			// TODO Why call FinitePrefix and not PetriNetUnfolder directly?
			return new FinitePrefix<>(mServices, mPetriNet).getResult();
		} catch (final AutomataOperationCanceledException ce) {
			final RunningTaskInfo runningTaskInfo = new RunningTaskInfo(getClass(), generateTimeoutMessage(mPetriNet));
			ce.addRunningTaskInfo(runningTaskInfo);
			throw ce;
		}
	}

	private ModifiableRetroMorphism<L, P> getRetromorphism(final IPetriNet<L, P> originalNet,
			final Map<Transition<L, P>, Transition<L, P>> copyMap) {
		final var retro = new ModifiableRetroMorphism<>(originalNet);
		for (final var entry : copyMap.entrySet()) {
			retro.addTransition(entry.getValue(), retro.getFirstTransitions(entry.getKey()),
					retro.getLastTransitions(entry.getKey()));
			retro.deleteTransition(entry.getKey());
		}
		return retro;
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
				mCoEnabledRelation, mMoverCheck, mPlaceFactory, true, mRun);
		final boolean result = rule.apply();
		mRun = rule.getAdaptedRun();
		return result;
	}

	/**
	 * @deprecated This wrapper is only supposed to exist temporarily
	 */
	@Deprecated(since = "2021-09-14")
	private boolean choiceRuleWrapper(final BoundedPetriNet<L, P> petriNet) {
		final ChoiceRule<L, P> rule = new ChoiceRule<>(mServices, mStatistics, petriNet, mCoEnabledRelation,
				mRetromorphism, mCompositionFactory, mRun);
		final boolean result = rule.apply();
		mRun = rule.getAdaptedRun();
		return result;
	}

	/**
	 * @deprecated This wrapper is only supposed to exist temporarily
	 */
	@Deprecated(since = "2022-10-07")
	private boolean sequenceRuleWrapper(final BoundedPetriNet<L, P> petriNet) {
		final SequenceRule<L, P> rule =
				new SequenceRule<>(mServices, mStatistics, petriNet, mCoEnabledRelation, mRetromorphism, mMoverCheck,
						mCompositionFactory, mPlaceFactory, mStuckPlaceChecker, mBranchingProcess, mRun);
		final boolean result = rule.apply();
		mRun = rule.getAdaptedRun();
		return result;
	}

	// ***************************************************** OUTPUT ****************************************************

	public BoundedPetriNet<L, P> getResult() {
		return mPetriNet;
	}

	public PetriNetRun<L, P> getAdaptedRun() {
		return mRun;
	}

	public LiptonReductionStatisticsGenerator getStatistics() {
		return mStatistics;
	}
}
