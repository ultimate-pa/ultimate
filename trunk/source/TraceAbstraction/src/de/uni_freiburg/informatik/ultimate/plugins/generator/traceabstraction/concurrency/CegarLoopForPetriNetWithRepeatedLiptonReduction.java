/*
 * Copyright (C) 2021 Dennis Wölfing
 * Copyright (C) 2021-2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021-2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionConcurrent plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionConcurrent plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstractionConcurrent plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoenabledRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ModifiableRetroMorphism;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.DefaultIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveDead;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveRedundantFlow;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.ICompositionFactoryWithBacktranslator;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe.PetriNetLargeBlockEncoding;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

/**
 * A CEGAR loop for Petri nets that repeatedly applies Lipton Reduction after each iteration.
 *
 * @author Dennis Wölfing
 *
 * @param <L>
 *            The type of the letters of the transitions.
 */
public class CegarLoopForPetriNetWithRepeatedLiptonReduction<L extends IIcfgTransition<?>>
		extends CegarLoopForPetriNet<L> {

	private final ICompositionFactoryWithBacktranslator<L> mCompositionFactory;
	private final IIndependenceCache<?, L> mIndependenceCache = new DefaultIndependenceCache<>();

	private ModifiableRetroMorphism<L, IPredicate> mFinitePrefixAbstractionRetromorphism;
	private CoenabledRelation<L, IPredicate> mCoEnabledRelationFromFinitePrefix;

	/**
	 * Construct the CEGAR loop.
	 *
	 * @param name
	 * @param rootNode
	 * @param csToolkit
	 * @param predicateFactory
	 * @param taPrefs
	 * @param errorLocs
	 * @param services
	 * @param compositionFactory
	 * @param transitionClazz
	 */
	public CegarLoopForPetriNetWithRepeatedLiptonReduction(final DebugIdentifier name,
			final BoundedPetriNet<L, IPredicate> initialAbstraction, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Set<IcfgLocation> errorLocs, final IUltimateServiceProvider services,
			final ICompositionFactoryWithBacktranslator<L> compositionFactory, final Class<L> transitionClazz,
			final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, services,
				transitionClazz, stateFactoryForRefinement);
		mCompositionFactory = compositionFactory;
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		// reset data from last iteration
		mFinitePrefixAbstractionRetromorphism = null;
		mCoEnabledRelationFromFinitePrefix = null;

		final boolean result = super.refineAbstraction();
		mAbstraction = applyLargeBlockEncoding(mAbstraction);
		return result;
	}

	protected BoundedPetriNet<L, IPredicate> applyLargeBlockEncoding(final BoundedPetriNet<L, IPredicate> cfg)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final long startTime = System.currentTimeMillis();

		final var counterexample = getCachedCounterexample();
		final PetriNetLargeBlockEncoding<L> lbe = new PetriNetLargeBlockEncoding<>(getServices(),
				mIcfg.getCfgSmtToolkit(), cfg, mPref.lbeIndependenceSettings(), mCompositionFactory, mPredicateFactory,
				mIndependenceCache, mFinitePrefixOfAbstraction, mFinitePrefixAbstractionRetromorphism,
				mCoEnabledRelationFromFinitePrefix, Set.of(counterexample));
		final BoundedPetriNet<L, IPredicate> lbecfg = lbe.getResult();

		mServices.getBacktranslationService().addTranslator(mCompositionFactory.getBacktranslator());
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, new StatisticsResult<>(Activator.PLUGIN_NAME,
				"PetriNetLargeBlockEncoding benchmarks", lbe.getStatistics()));

		final var adaptedRun = lbe.getAdaptedRuns().get(counterexample);
		if (adaptedRun != null) {
			assert adaptedRun.isRunOf(lbecfg) : "adaptation produced invalid run!";
			mCounterexampleCache.setCounterexample(adaptedRun);
		} else if (counterexample != null) {
			// This can currently happen, because run adaptation does not support post-scripts.
			// The code below is a workaround that may succeed in a few cases.

			mLogger.error("Lipton reduction run adaptation of counterexample failed.");
			if (!lbecfg.getAlphabet().containsAll(counterexample.getWord().asSet())) {
				throw new AssertionError("Lipton reduction run adaptation failed, and the cached counterexample word"
						+ " contains letters no longer in the reduced abstraction's alphabet!");
			}

			final var run = new Accepts<>(new AutomataLibraryServices(mServices), lbecfg, counterexample.getWord())
					.getAcceptingRun();
			if (run == null) {
				throw new AssertionError("Lipton reduction run adaptation failed, "
						+ "and the cached counterexample word is no longer accepted by reduced abstraction!");
			}
			assert run.isRunOf(lbecfg) : "Run returned by Accepts() is not truly a run of the net";

			mLogger.warn("Successfully replayed original counterexample word on reduced net.");
			mCounterexampleCache.setCounterexample(run);
		}

		final long endTime = System.currentTimeMillis();
		final long difference = endTime - startTime;
		mLogger.info("Time needed for LBE in milliseconds: " + difference);

		return lbecfg;
	}

	private PetriNetRun<L, IPredicate> getCachedCounterexample()
			throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		final var cached = mCounterexampleCache.getCounterexample();
		if (!USE_COUNTEREXAMPLE_CACHE || cached == null) {
			return null;
		}
		if (cached.isRunOf(mAbstraction)) {
			return cached;
		}

		// Depending on which optimizations (RemoveDead, RemoveRedundantFlow, USE_ON_DEMAND_RESULT) are turned on in
		// CegarLoopForPetriNet, the cached counterexample may (depending on settings) not be a run of the abstraction
		// (the transitions and markings may not match the Petri net). However, we still expect the counterexample word
		// to be accepted by the abstraction.
		// To account for such cases, we simply check acceptance and retrieve the accepting run in the new abstraction.
		mLogger.warn("Counterexample is not a run of mAbstraction. Replaying acceptance of the word...");
		final var run =
				new Accepts<>(new AutomataLibraryServices(mServices), mAbstraction, cached.getWord()).getAcceptingRun();
		if (run == null) {
			throw new AssertionError("Cached counterexample (word) is not accepted by current abstraction!");
		}
		assert run.isRunOf(mAbstraction) : "Run returned by Accepts is not truly a run of the net";

		return run;
	}

	@Override
	protected void reduceSizeOfAbstraction() throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final var sizeReduction = getReductionToApplyAfterDifference();
		if (sizeReduction == SizeReduction.NONE) {
			return;
		}

		assert mFinitePrefixAbstractionRetromorphism == null : "Composition of retromorphisms not yet supported here";
		assert mCoEnabledRelationFromFinitePrefix == null : "Unexpected coenabled relation";

		final var originalAbstraction = mAbstraction;
		final Map<Transition<L, IPredicate>, Transition<L, IPredicate>> old2New;
		switch (sizeReduction) {
		case REMOVE_DEAD:
			final var removeDead = new RemoveDead<>(new AutomataLibraryServices(getServices()), mAbstraction,
					mFinitePrefixOfAbstraction, true);
			mAbstraction = removeDead.getResult();
			old2New = removeDead.getOldToNew();
			break;
		case REMOVE_REDUNDANT_FLOW:
			final var removeRedundantFlow = new RemoveRedundantFlow<>(new AutomataLibraryServices(mServices),
					mAbstraction, mFinitePrefixOfAbstraction, null, null);
			mAbstraction = removeRedundantFlow.getResult();
			old2New = removeRedundantFlow.getOld2projected();

			// Dominik 2022-12-09: I don't know how to adapt the coenabled relation in this case.
			// Hence clear the finite prefix, and let the Lipton reduction compute a fresh one.
			mFinitePrefixOfAbstraction = null;
			break;
		default:
			throw new IllegalArgumentException("Unknown size reduction: " + sizeReduction);
		}

		if (mFinitePrefixOfAbstraction != null) {
			mCoEnabledRelationFromFinitePrefix = CoenabledRelation.fromBranchingProcess(mFinitePrefixOfAbstraction);
			mCoEnabledRelationFromFinitePrefix.renameAndProjectTransitions(old2New);

			mFinitePrefixAbstractionRetromorphism = new ModifiableRetroMorphism<>(originalAbstraction);
			mFinitePrefixAbstractionRetromorphism.renameAndProjectTransitions(old2New);
		}
	}
}
