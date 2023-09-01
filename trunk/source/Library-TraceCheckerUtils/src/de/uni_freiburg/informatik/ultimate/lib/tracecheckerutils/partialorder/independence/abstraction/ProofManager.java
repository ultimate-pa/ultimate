/*
 * Copyright (C) 2023 Veronika Klasen
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.dynamicabstraction.IProofManager;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;

/**
 * Used by DynamicStratifiedReduction to handle everything related to proofs
 *
 * @param <L>
 *            The type of actions
 * @param <H>
 *            The type of abstraction levels
 * @param <P>
 *            The type of proofs returned by a refinement engine
 */

public class ProofManager<L extends IAction, H, P> implements IProofManager<H, IPredicate> {
	private final ILogger mLogger;
	private final IRefinableAbstraction<P, H, L> mAbstraction;
	private final Function<IPredicate, List<IPredicate>> mGetConjuncts;
	private final Predicate<IPredicate> mIsErrorState;

	private final Statistics mStatistics = new Statistics();

	private final List<H> mProofLevels = new ArrayList<>();

	// count how many times each proof has been chosen as responsible
	private final List<Integer> mProofCounter = new ArrayList<>();

	// the proof we chose at the last proven state
	private int mLastResponsibleProof = -1;

	public ProofManager(final IUltimateServiceProvider services, final IRefinableAbstraction<P, H, L> abstraction,
			final Function<IPredicate, List<IPredicate>> getConjuncts, final Predicate<IPredicate> isErrorState) {
		mLogger = services.getLoggingService().getLogger(getClass());
		mAbstraction = abstraction;
		mGetConjuncts = getConjuncts;
		mIsErrorState = isErrorState;
	}

	public void addProof(final IRefinementEngineResult<L, P> proof) {
		final var proofAbstraction = mAbstraction.refine(mAbstraction.getInitial(), proof);
		mProofLevels.add(proofAbstraction);

		// reset all proof counters and add this iteration's irresp. proofs to statistics
		for (int i = 0; i < mProofCounter.size(); i++) {
			if (mProofCounter.get(i) == 0) {
				mStatistics.addIrresponsibleProofs(1);
			}
			mProofCounter.set(i, 0);
		}

		// TODO
		mProofCounter.add(0);
	}

	@Override
	public boolean isProvenState(final IPredicate state) {
		return mIsErrorState.test(state)
				&& mGetConjuncts.apply(state).stream().anyMatch(p -> SmtUtils.isFalseLiteral(p.getFormula()));
	}

	@Override
	public H chooseResponsibleAbstraction(final IPredicate state) {
		// get conjuncts of the state
		final List<IPredicate> conjuncts = mGetConjuncts.apply(state);

		// identify candidates for responsible proofs (proofs whose conjunct is FALSE)
		final var candidateProofs =
				IntStream.range(0, conjuncts.size()).filter(i -> SmtUtils.isFalseLiteral(conjuncts.get(i).getFormula()))
						.mapToObj(Integer::valueOf).collect(Collectors.toList());
		assert !candidateProofs.isEmpty() : "No proof can be made responsible for state " + state;

		// choose the proof that is deemed responsible for state being a proven state
		final int responsibleProof;
		// Priorities:
		if (candidateProofs.contains(mLastResponsibleProof)) {
			// (1) last chosen proof
			responsibleProof = mLastResponsibleProof;
		} else {
			// (2) number of times chosen (asc.)
			// (3) refinement round the proof was found in (desc.)
			responsibleProof = candidateProofs.stream()
					.sorted(Comparator.<Integer, Integer> comparing(p -> mProofCounter.get(p)).thenComparing(p -> -p))
					.findFirst().get();
		}

		// update mLastResponsibleProof and mProofCounter
		mLastResponsibleProof = responsibleProof;
		mProofCounter.set(responsibleProof, mProofCounter.get(responsibleProof) + 1);

		// return abstraction corresponding to the chosen proof
		return mProofLevels.get(responsibleProof);
	}

	public void finish() {
		// TODO collect statistics from last iteration
		for (final int i : mProofCounter) {
			if (i == 0) {
				mStatistics.addIrresponsibleProofs(1);
			}
		}
	}

	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private static final class Statistics extends AbstractStatisticsDataProvider {
		private int mIrresponsibleProofs = 0;

		public Statistics() {
			declare("IrresponsibleProofs", () -> mIrresponsibleProofs, KeyType.COUNTER);
		}

		public void addIrresponsibleProofs(final int n) {
			mIrresponsibleProofs += n;
		}
	}
}
