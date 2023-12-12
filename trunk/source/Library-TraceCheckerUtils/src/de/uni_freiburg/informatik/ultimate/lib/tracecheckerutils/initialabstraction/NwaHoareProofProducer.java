/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ProductNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.proofs.IProofPostProcessor;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.proofs.IProofProducer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.floydhoare.HoareAnnotationComposer;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.floydhoare.HoareAnnotationExtractor;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.floydhoare.HoareAnnotationFragments;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.floydhoare.IFloydHoareAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.proofs.IFinishWithFinalAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.proofs.IUpdateOnDifference;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.proofs.IUpdateOnMinimization;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

final class NwaHoareProofProducer<L extends IAction, PROGRAM, PROOF>
		implements IProofProducer<PROGRAM, PROOF>, IUpdateOnMinimization<L>, IUpdateOnDifference<L>,
		IFinishWithFinalAbstraction<INestedWordAutomaton<L, IPredicate>> {

	private final IUltimateServiceProvider mServices;

	private final INestedWordAutomaton<L, IPredicate> mProgram;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;

	private final HoareProofSettings mPrefs;
	private final Set<IPredicate> mHoareAnnotationStates;

	private final IProofPostProcessor<INestedWordAutomaton<L, IPredicate>, IFloydHoareAnnotation<IPredicate>, PROGRAM, PROOF> mPost;

	private final HoareAnnotationFragments<L> mHaf;

	private INestedWordAutomaton<L, IPredicate> mFinalAbstraction;

	private NwaHoareProofProducer(final IUltimateServiceProvider services,
			final INestedWordAutomaton<L, IPredicate> program, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final HoareProofSettings prefs,
			final Set<IPredicate> hoareAnnotationStates,
			final IProofPostProcessor<INestedWordAutomaton<L, IPredicate>, IFloydHoareAnnotation<IPredicate>, PROGRAM, PROOF> postProcessor) {
		mServices = services;
		mProgram = program;
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;
		mPrefs = prefs;
		mHoareAnnotationStates = hoareAnnotationStates;
		mHaf = new HoareAnnotationFragments<>(services.getLoggingService().getLogger(getClass()),
				hoareAnnotationStates);
		mPost = postProcessor;

		assert postProcessor.getOriginalProgram() == mProgram;
	}

	public static <L extends IAction>
			NwaHoareProofProducer<L, INestedWordAutomaton<L, IPredicate>, IFloydHoareAnnotation<IPredicate>>
			create(final IUltimateServiceProvider services, final INestedWordAutomaton<L, IPredicate> program,
					final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
					final HoareProofSettings prefs, final Set<IPredicate> hoareAnnotationStates) {
		return new NwaHoareProofProducer<>(services, program, csToolkit, predicateFactory, prefs, hoareAnnotationStates,
				IProofPostProcessor.identity(program));
	}

	@Override
	public PROGRAM getProgram() {
		return mPost.getOriginalProgram();
	}

	@Override
	public boolean hasProof() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public PROOF getOrComputeProof() {
		// TODO measure time
		// mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.HoareAnnotationTime.toString());
		try {
			final HoareAnnotationComposer clha = computeHoareAnnotationComposer();

			// TODO extract data to IFloydHoareAnnotation
			// final HoareAnnotationWriter writer = new HmComputeHoareAnnotationoareAnnotationWriter(mIcfg, mCsToolkit,
			// mPredicateFactory,
			// clha,
			// mServices, mSimplificationTechnique, mXnfConversionTechnique);
			// writer.addHoareAnnotationToCFG();

			// TODO forward statistics
			// mCegarLoopBenchmark.addHoareAnnotationData(clha.getHoareAnnotationStatisticsGenerator());
		} finally {
			// mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.HoareAnnotationTime.toString());
		}

		// TODO
		final IFloydHoareAnnotation<IPredicate> floydHoare = null;
		return mPost.processProof(floydHoare);
	}

	private HoareAnnotationComposer computeHoareAnnotationComposer() {
		if (mCsToolkit.getManagedScript().isLocked()) {
			throw new AssertionError(
					"ManagedScript must not be locked at the beginning of Hoare annotation computation");
		}
		new HoareAnnotationExtractor<>(mServices, mFinalAbstraction, mHaf);
		final HoareAnnotationComposer clha = new HoareAnnotationComposer(mCsToolkit, mPredicateFactory, mHaf, mServices,
				mPrefs.getSimplificationTechnique(), mPrefs.getXnfConversionTechnique());
		return clha;
	}

	@Override
	public <OUTPROGRAM, OUTPROOF> NwaHoareProofProducer<L, OUTPROGRAM, OUTPROOF>
			withPostProcessor(final IProofPostProcessor<PROGRAM, PROOF, OUTPROGRAM, OUTPROOF> postProcessor) {
		return new NwaHoareProofProducer<>(mServices, mProgram, mCsToolkit, mPredicateFactory, mPrefs,
				mHoareAnnotationStates, IProofPostProcessor.compose(mPost, postProcessor));
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
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
}