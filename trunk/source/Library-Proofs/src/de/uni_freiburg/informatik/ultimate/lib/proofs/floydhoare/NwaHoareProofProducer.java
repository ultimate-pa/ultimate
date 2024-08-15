/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare;

import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ProductNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.proofs.IProofProducer;
import de.uni_freiburg.informatik.ultimate.lib.proofs.PrePostConditionSpecification;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;
import de.uni_freiburg.informatik.ultimate.util.statistics.TimeTracker;

/**
 * Produces a Floyd/Hoare annotation for a nested-word automaton.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the program automaton
 */
public final class NwaHoareProofProducer<L extends IAction>
		implements IProofProducer<INestedWordAutomaton<L, IPredicate>, IFloydHoareAnnotation<IPredicate>> {

	private final IUltimateServiceProvider mServices;
	private final INestedWordAutomaton<L, IPredicate> mProgram;
	private final PrePostConditionSpecification<IPredicate> mSpecification;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;

	private final HoareProofSettings mPrefs;

	private final HoareAnnotationFragments<L> mHaf;
	private INestedWordAutomaton<L, IPredicate> mFinalAbstraction;

	private IFloydHoareAnnotation<IPredicate> mProof;
	private final Statistics mStatistics;

	public NwaHoareProofProducer(final IUltimateServiceProvider services,
			final INestedWordAutomaton<L, IPredicate> program, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final HoareProofSettings prefs,
			final Set<IPredicate> hoareAnnotationStates) {
		mServices = services;
		mProgram = program;
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;
		mPrefs = prefs;
		mHaf = new HoareAnnotationFragments<>(hoareAnnotationStates);

		mSpecification = new PrePostConditionSpecification<>(program.getInitialStates(), program::isFinal,
				predicateFactory.and(), predicateFactory.or());

		mStatistics = new Statistics();
	}

	public static Set<IPredicate> computeHoareStates(final IIcfg<? extends IcfgLocation> icfg,
			final INestedWordAutomaton<?, IPredicate> abstraction, final HoareAnnotationPositions hoarePositions) {
		final var hoareLocs = hoarePositions.getLocations(icfg);
		return abstraction.getStates().stream()
				.filter(p -> PredicateUtils.streamLocations(p).anyMatch(hoareLocs::contains))
				.collect(Collectors.toSet());
	}

	@Override
	public INestedWordAutomaton<L, IPredicate> getProgram() {
		return mProgram;
	}

	@Override
	public boolean isReadyToComputeProof() {
		return mFinalAbstraction != null;
	}

	@Override
	public IFloydHoareAnnotation<IPredicate> getOrComputeProof() {
		if (mProof == null) {
			mProof = computeProof();
		}
		return mProof;
	}

	private IFloydHoareAnnotation<IPredicate> computeProof() {
		return mStatistics.measureProofComputation(() -> {
			final HoareAnnotationComposer clha = computeHoareAnnotationComposer();
			final var floydHoare = clha.extractAnnotation(mSpecification);
			mStatistics.reportHoareStatistics(clha);
			return floydHoare;
		});
	}

	private HoareAnnotationComposer computeHoareAnnotationComposer() {
		if (mCsToolkit.getManagedScript().isLocked()) {
			throw new AssertionError(
					"ManagedScript must not be locked at the beginning of Hoare annotation computation");
		}
		new HoareAnnotationExtractor<>(mServices, mFinalAbstraction, mHaf);
		return new HoareAnnotationComposer(mCsToolkit, mPredicateFactory, mHaf, mServices);
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	public boolean exploitSigmaStarConcatOfIa() {
		return false;
	}

	public void updateOnIntersection(
			final Map<IPredicate, Map<IPredicate, ProductNwa<L, IPredicate>.ProductState>> fst2snd2res,
			final IDoubleDeckerAutomaton<L, IPredicate> result) {
		mHaf.updateOnIntersection(fst2snd2res, result);
	}

	public void addDeadEndDoubleDeckers(final IOpWithDelayedDeadEndRemoval<L, IPredicate> diff) {
		mHaf.addDeadEndDoubleDeckers(diff);
	}

	public void updateOnMinimization(final Map<IPredicate, IPredicate> old2New,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction) {
		mHaf.updateOnMinimization(old2New, abstraction);
	}

	public void finish(final INestedWordAutomaton<L, IPredicate> finalAbstraction) {
		mFinalAbstraction = finalAbstraction;
	}

	private static final class Statistics extends AbstractStatisticsDataProvider {
		private final TimeTracker mProofTime = new TimeTracker();

		public Statistics() {
			declare("Hoare annotation time", () -> mProofTime, KeyType.TT_TIMER);
		}

		private <T> T measureProofComputation(final Supplier<T> computation) {
			return mProofTime.measure(computation);
		}

		private void reportHoareStatistics(final HoareAnnotationComposer composer) {
			forward("Hoare annotation statistics", composer::getHoareAnnotationStatisticsGenerator);
		}
	}
}