/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.IFloydHoareAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.TransformFloydHoareAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class NaiveOwickiGries<L extends IAction, P> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final BasicPredicateFactory mPredicateFactory;
	private final CfgSmtToolkit mCsToolkit;
	private final IPetriNet<L, P> mProgram;
	private final OwickiGriesSettings mSettings;

	private final Statistics mStatistics = new Statistics();

	public NaiveOwickiGries(final IUltimateServiceProvider services, final BasicPredicateFactory predicateFactory,
			final CfgSmtToolkit csToolkit, final IPetriNet<L, P> program, final OwickiGriesSettings settings) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mPredicateFactory = predicateFactory;
		mCsToolkit = csToolkit;
		mProgram = program;
		mSettings = settings;
	}

	public IPetriNetProofProducer<L, P> createProofProducer(final Function<P, IPredicate> assertionPlaceToAssertion) {
		return new Producer(assertionPlaceToAssertion);
	}

	/**
	 *
	 * @param <S>
	 * @param marking2State
	 *            Map from reachable markings to corresponding states.
	 *
	 *            Reachable markings whose Floyd-Hoare annotation is {@code true} may be omitted. This is useful e.g.
	 *            for optimizations that prune reachable markings from which no accepting place can be reached.
	 * @return
	 */
	public <S> Function<IFloydHoareAnnotation<S>, OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>>>
			createProofConverter(final Map<Marking<P>, S> marking2State) {
		return floydHoare -> {
			final var map = new BidirectionalMap<Marking<P>, S>();
			map.putAll(marking2State);

			// Convert IFloydHoareAnnotation of automaton to IFloydHoareAnnotation of Petri reachability graph.
			// We use truePredicate as fallback annotation.
			final IPredicate truePredicate = mPredicateFactory.and();
			final var markingFloydHoare =
					new TransformFloydHoareAnnotation<>(floydHoare, map.values(), map.inverse()::get, truePredicate)
							.getResult();

			assert checkFloydHoareValidity(markingFloydHoare) : "Invalid Floyd-Hoare annotation";

			// Explicitly compute reachable markings. In contrast to marking2State.keySet(), this may not omit any
			// reachable markings no matter what their Floyd-Hoare annotation would be.
			final Collection<Marking<P>> reachableMarkings;
			try {
				reachableMarkings = PetriFloydHoare.computeReachableMarkings(mProgram);
			} catch (final PetriNetNot1SafeException e) {
				throw new AssertionError(e);
			}

			return convertToOwickiGries(markingFloydHoare, reachableMarkings);
		};
	}

	public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> convertToOwickiGries(
			final IFloydHoareAnnotation<Marking<P>> floydHoare, final Collection<Marking<P>> reachableMarkings) {
		final long startTime = System.currentTimeMillis();

		final OwickiGriesConstruction<L, P> construction = new OwickiGriesConstruction<>(mServices, mCsToolkit,
				mProgram, reachableMarkings, floydHoare, mSettings.useHittingSets());
		mLogger.info("Computed Owicki-Gries annotation of size %d in %d ms", construction.getResult().size(),
				System.currentTimeMillis() - startTime);

		assert checkOwickiGriesValidity(construction.getResult()) : "Invalid Owicki-Gries annotation";
		return construction.getResult();
	}

	private boolean checkFloydHoareValidity(final IFloydHoareAnnotation<Marking<P>> floydHoare) {
		final long startTime = System.currentTimeMillis();
		final Validity validity;
		try {
			validity = new PetriFloydHoareValidityCheck<>(mServices, mCsToolkit.getManagedScript(),
					mCsToolkit.getModifiableGlobalsTable(), mProgram, floydHoare).isValid();
			if (validity == Validity.UNKNOWN) {
				mLogger.warn("Could not prove validity of Floyd-Hoare annotation for Petri reachability graph");
			}
			return validity != Validity.INVALID;
		} catch (final PetriNetNot1SafeException e) {
			throw new AssertionError(e);
		} finally {
			final long elapsed = System.currentTimeMillis() - startTime;
			mLogger.info("Checked validity of Floyd-Hoare annotation for Petri reachability graph in %d ms", elapsed);
		}
	}

	private boolean
			checkOwickiGriesValidity(final OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> ogConstruction) {
		final long startTime = System.currentTimeMillis();
		try {
			final var validity =
					new PetriOwickiGriesValidityCheck<>(mServices, mProgram, mCsToolkit, ogConstruction).isValid();
			assert validity != Validity.INVALID : "Owicki-Gries annotation is invalid";
			if (validity == Validity.UNKNOWN) {
				mLogger.warn("Could not prove validity of Owicki-Gries annotation");
			}
			return validity != Validity.INVALID;
		} finally {
			final long elapsed = System.currentTimeMillis() - startTime;
			mLogger.info("Checked validity of Owicki-Gries annotation for Petri net in %d ms", elapsed);
		}
	}

	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private static class Statistics extends AbstractStatisticsDataProvider {
		// TODO measure times and sizes
	}

	private class Producer implements IPetriNetProofProducer<L, P> {
		private final Function<P, IPredicate> mAssertionPlaceToAssertion;

		private final List<IPredicateCoverageChecker> mCoverageRelations = new ArrayList<>();
		private IPetriNet<L, P> mFinalAbstraction;

		private Producer(final Function<P, IPredicate> assertionPlaceToAssertion) {
			mAssertionPlaceToAssertion = assertionPlaceToAssertion;
		}

		@Override
		public void refine(final IRefinementEngineResult<L, ?> refinementResult,
				final INestedWordAutomaton<L, IPredicate> interpolantAutomaton,
				final Map<Transition<L, P>, Transition<L, P>> transitionBacktranslation) {
			if (mSettings.useCoveringSimplification()) {
				mCoverageRelations.add(refinementResult.getPredicateUnifier().getCoverageRelation());
			}
		}

		@Override
		public void finalize(final IPetriNet<L, P> refinedNet, final BranchingProcess<L, P> refinedNetUnfolding) {
			mFinalAbstraction = refinedNet;
		}

		@Override
		public IPetriNet<L, P> getProgram() {
			return mProgram;
		}

		@Override
		public boolean isReadyToComputeProof() {
			return mFinalAbstraction != null;
		}

		@Override
		public OwickiGriesAnnotation<Transition<L, P>, P, Marking<P>> getOrComputeProof() {
			// compute the Floyd-Hoare annotation
			PetriFloydHoare<L, P> petriFloydHoare;
			try {
				petriFloydHoare = new PetriFloydHoare<>(mPredicateFactory, mProgram, mFinalAbstraction,
						mAssertionPlaceToAssertion, mCoverageRelations, mSettings.useCoveringSimplification());
			} catch (final PetriNetNot1SafeException e) {
				throw new AssertionError(e);
			}

			// convert the Floyd-Hoare annotation to Owicki-Gries
			return convertToOwickiGries(petriFloydHoare.getResult(), petriFloydHoare.getReachableMarkings());
		}

		@Override
		public IStatisticsDataProvider getStatistics() {
			return NaiveOwickiGries.this.getStatistics();
		}
	}
}
