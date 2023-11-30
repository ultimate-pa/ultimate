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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ProductNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.proofs.IProofPostProcessor;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.proofs.IProofProducer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.floydhoare.IFloydHoareAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.proofs.IUpdateOnDifference;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.proofs.IUpdateOnMinimization;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

final class NwaHoareProofProducer<L extends IAction, S, PROGRAM, PROOF>
		implements IProofProducer<PROGRAM, PROOF>, IUpdateOnMinimization<L>, IUpdateOnDifference<L> {

	private final INestedWordAutomaton<L, S> mProgram;
	// private final Set<S> mHoareAnnotationStates;
	private final IProofPostProcessor<INestedWordAutomaton<L, S>, IFloydHoareAnnotation<L, IPredicate>, PROGRAM, PROOF> mPost;

	private NwaHoareProofProducer(final INestedWordAutomaton<L, S> program, // final Set<S> hoareAnnotationStates,
			final IProofPostProcessor<INestedWordAutomaton<L, S>, IFloydHoareAnnotation<L, IPredicate>, PROGRAM, PROOF> postProcessor) {
		mProgram = program;
		// mHoareAnnotationStates = hoareAnnotationStates;
		// mHaf = new HoareAnnotationFragments<>(mLogger, hoareAnnotationStates);
		mPost = postProcessor;

		assert postProcessor.getOriginalProgram() == mProgram;
	}

	public static <L extends IAction, S>
			NwaHoareProofProducer<L, S, INestedWordAutomaton<L, S>, IFloydHoareAnnotation<L, IPredicate>>
			create(final INestedWordAutomaton<L, S> program
	// , final Set<S> hoareAnnotationStates
	) {
		return new NwaHoareProofProducer<>(program,
				// hoareAnnotationStates,
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
		// TODO
		final IFloydHoareAnnotation<L, IPredicate> floydHoare = null;
		return mPost.processProof(floydHoare);
	}

	@Override
	public <OUTPROGRAM, OUTPROOF> NwaHoareProofProducer<L, S, OUTPROGRAM, OUTPROOF>
			withPostProcessor(final IProofPostProcessor<PROGRAM, PROOF, OUTPROGRAM, OUTPROOF> postProcessor) {
		return new NwaHoareProofProducer<>(mProgram, // mHoareAnnotationStates,
				IProofPostProcessor.compose(mPost, postProcessor));
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
		// TODO Auto-generated method stub

	}

	@Override
	public void addDeadEndDoubleDeckers(final IOpWithDelayedDeadEndRemoval<L, IPredicate> diff) {
		// TODO Auto-generated method stub

	}

	@Override
	public void updateOnMinimization(final Map<IPredicate, IPredicate> old2New,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction) {
		// TODO Auto-generated method stub

	}
}