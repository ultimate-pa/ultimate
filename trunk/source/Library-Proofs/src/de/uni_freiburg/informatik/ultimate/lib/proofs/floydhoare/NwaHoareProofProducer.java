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
import de.uni_freiburg.informatik.ultimate.lib.proofs.AbstractProofProducer;
import de.uni_freiburg.informatik.ultimate.lib.proofs.IFinishWithFinalAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.proofs.IProofPostProcessor;
import de.uni_freiburg.informatik.ultimate.lib.proofs.IUpdateOnDifference;
import de.uni_freiburg.informatik.ultimate.lib.proofs.IUpdateOnMinimization;
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
 * @param <A>
 *            The type of abstraction for which a proof is produced. By default, this is {@link INestedWordAutomaton},
 *            but it may differ if the proof is post-processed (see {@link #withPostProcessor(IProofPostProcessor)}.
 * @param <P>
 *            The type of proof which is produced. By default, this is {@link IFloydHoareAnnotation}, but it may differ
 *            if the proof is post-processed (see {@link #withPostProcessor(IProofPostProcessor)}.
 */
public final class NwaHoareProofProducer<L extends IAction, A, P>
		extends AbstractProofProducer<A, P, INestedWordAutomaton<L, IPredicate>, IFloydHoareAnnotation<IPredicate>>
		implements IUpdateOnMinimization<L>, IUpdateOnDifference<L>,
		IFinishWithFinalAbstraction<INestedWordAutomaton<L, IPredicate>> {

	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;

	private final HoareProofSettings mPrefs;
	private final Set<IPredicate> mHoareAnnotationStates;

	private final HoareAnnotationFragments<L> mHaf;
	private INestedWordAutomaton<L, IPredicate> mFinalAbstraction;
	private final Statistics mStatistics;

	private NwaHoareProofProducer(final IUltimateServiceProvider services,
			final INestedWordAutomaton<L, IPredicate> program, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final HoareProofSettings prefs,
			final Set<IPredicate> hoareAnnotationStates,
			final IProofPostProcessor<INestedWordAutomaton<L, IPredicate>, IFloydHoareAnnotation<IPredicate>, A, P> postProcessor) {
		super(program, postProcessor);

		mServices = services;
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;
		mPrefs = prefs;
		mHoareAnnotationStates = hoareAnnotationStates;
		mHaf = new HoareAnnotationFragments<>(services.getLoggingService().getLogger(getClass()),
				hoareAnnotationStates);

		mStatistics = new Statistics(mPost);
	}

	/**
	 * Creates a new proof producer without any postprocessing.
	 *
	 * @param <L>
	 *            the type of letters in the program automaton for which a proof is produced
	 * @param services
	 * @param program
	 * @param csToolkit
	 * @param predicateFactory
	 * @param prefs
	 * @param hoareAnnotationStates
	 *            The states for which a Hoare annotation shall be produced. This can be a subset of the program
	 *            automaton's states.
	 * @return
	 */
	public static <L extends IAction>
			NwaHoareProofProducer<L, INestedWordAutomaton<L, IPredicate>, IFloydHoareAnnotation<IPredicate>>
			create(final IUltimateServiceProvider services, final INestedWordAutomaton<L, IPredicate> program,
					final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
					final HoareProofSettings prefs, final Set<IPredicate> hoareAnnotationStates) {
		return new NwaHoareProofProducer<>(services, program, csToolkit, predicateFactory, prefs, hoareAnnotationStates,
				IProofPostProcessor.identity(program));
	}

	public static Set<IPredicate> computeHoareStates(final IIcfg<? extends IcfgLocation> icfg,
			final INestedWordAutomaton<?, IPredicate> abstraction, final HoareAnnotationPositions hoarePositions) {
		final var hoareLocs = hoarePositions.getLocations(icfg);
		return abstraction.getStates().stream()
				.filter(p -> PredicateUtils.getLocations(p).anyMatch(hoareLocs::contains)).collect(Collectors.toSet());
	}

	@Override
	public boolean hasProof() {
		return mFinalAbstraction != null;
	}

	@Override
	protected IFloydHoareAnnotation<IPredicate> computeProof() {
		return mStatistics.measureProofComputation(() -> {
			final HoareAnnotationComposer clha = computeHoareAnnotationComposer();
			final var floydHoare = clha.extractAnnotation();
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
	public <A2, P2> NwaHoareProofProducer<L, A2, P2>
			withPostProcessor(final IProofPostProcessor<A, P, A2, P2> postProcessor) {
		return new NwaHoareProofProducer<>(mServices, mProgram, mCsToolkit, mPredicateFactory, mPrefs,
				mHoareAnnotationStates, IProofPostProcessor.compose(mPost, postProcessor));
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	@Override
	public boolean exploitSigmaStarConcatOfIa() {
		return false;
	}

	@Override
	public void updateOnIntersection(
			final Map<IPredicate, Map<IPredicate, ProductNwa<L, IPredicate>.ProductState>> fst2snd2res,
			final IDoubleDeckerAutomaton<L, IPredicate> result) {
		mHaf.updateOnIntersection(fst2snd2res, result);
	}

	@Override
	public void addDeadEndDoubleDeckers(final IOpWithDelayedDeadEndRemoval<L, IPredicate> diff) {
		mHaf.addDeadEndDoubleDeckers(diff);
	}

	@Override
	public void updateOnMinimization(final Map<IPredicate, IPredicate> old2New,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction) {
		mHaf.updateOnMinimization(old2New, abstraction);
	}

	@Override
	public void finish(final INestedWordAutomaton<L, IPredicate> finalAbstraction) {
		mFinalAbstraction = finalAbstraction;
	}

	private static final class Statistics extends AbstractStatisticsDataProvider {
		private final TimeTracker mProofTime = new TimeTracker();

		public Statistics(final IProofPostProcessor<?, ?, ?, ?> post) {
			declare("Hoare annotation time", () -> mProofTime, KeyType.TT_TIMER);
			forward("Postprocessor statistics", post::getStatistics);
		}

		private <T> T measureProofComputation(final Supplier<T> computation) {
			return mProofTime.measure(computation);
		}

		private void reportHoareStatistics(final HoareAnnotationComposer composer) {
			forward("Hoare annotation statistics", composer::getHoareAnnotationStatisticsGenerator);
		}
	}
}