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

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.CopySubnet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

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

	private BoundedPetriNet<L, P> mResult;
	private final LiptonReductionStatisticsGenerator mStatistics = new LiptonReductionStatisticsGenerator();

	private final ModifiableRetroMorphism<L, P> mRetromorphism;

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
		mStuckPlaceChecker = stuckPlaceChecker;
		mIndependenceCache = cache;

		mPetriNet = CopySubnet.copy(mServices, petriNet, new HashSet<>(petriNet.getTransitions()),
				new HashSet<>(petriNet.getAlphabet()), true);
		mRetromorphism = new ModifiableRetroMorphism<>(mPetriNet);
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
			// TODO Why call FinitePrefix and not PetriNetUnfolder directly?
			mBranchingProcess = new FinitePrefix<>(mServices, mPetriNet).getResult();
			mBranchingProcess.getEvents().stream().filter(Event::isCutoffEvent)
					.forEach(e -> mCutOffs.addPair(e.getCompanion(), e));
			mCoEnabledRelation = CoenabledRelation.fromBranchingProcess(mBranchingProcess);

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
			mResult = mPetriNet;

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

	/**
	 * @deprecated This wrapper is only supposed to exist temporarily
	 */
	@Deprecated(since = "2021-09-15")
	private boolean synthesizeLockRuleWrapper(final BoundedPetriNet<L, P> petriNet) {
		final SynthesizeLockRule<L, P> rule = new SynthesizeLockRule<>(mServices, mStatistics, petriNet,
				mCoEnabledRelation, mIndependenceCache, mMoverCheck, mPlaceFactory, true);
		return rule.apply();
	}

	/**
	 * @deprecated This wrapper is only supposed to exist temporarily
	 */
	@Deprecated(since = "2021-09-14")
	private boolean choiceRuleWrapper(final BoundedPetriNet<L, P> petriNet) {
		final ChoiceRule<L, P> rule = new ChoiceRule<>(mServices, mStatistics, petriNet, mCoEnabledRelation,
				mRetromorphism, mCompositionFactory, mIndependenceCache);
		return rule.apply();
	}

	/**
	 * @deprecated This wrapper is only supposed to exist temporarily
	 */
	@Deprecated(since = "2022-10-07")
	private boolean sequenceRuleWrapper(final BoundedPetriNet<L, P> petriNet) {
		final SequenceRule<L, P> rule =
				new SequenceRule<>(mServices, mStatistics, petriNet, mCoEnabledRelation, mRetromorphism, mMoverCheck,
						mCompositionFactory, mPlaceFactory, mIndependenceCache, mStuckPlaceChecker, mBranchingProcess);
		return rule.apply();
	}

	// ***************************************************** OUTPUT ****************************************************

	public BoundedPetriNet<L, P> getResult() {
		return mResult;
	}

	public LiptonReductionStatisticsGenerator getStatistics() {
		return mStatistics;
	}
}
