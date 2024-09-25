/*
 * Copyright (C) 2024 Marcel Ebbinghaus
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.MLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderReductionFacade.StateSplitter;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Criterion for conditional commutativity checking with limited checks.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
public class LimitedChecksCriterion<L> implements IConditionalCommutativityCriterion<L> {
	private final Map<Pair<L, L>, Integer> mStatementMap = new HashMap<>();
	private final int mLimit;

	public LimitedChecksCriterion(final int limit) {
		mLimit = limit;
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean decide(final IPredicate state, final L letter1, final L letter2) {
		final Pair<L, L> pair = new Pair<>(letter1, letter2);
		return !(mStatementMap.containsKey(pair) && mStatementMap.get(pair) == mLimit);
	}

	@Override
	public boolean decide(final IPredicate condition) {
		return true;
	}

	@Override
	public void updateCriterion(final IPredicate state, final L letter1, final L letter2) {
		final Pair<L, L> pair = new Pair<>(letter1, letter2);
		if (!mStatementMap.containsKey(pair)) {
			mStatementMap.put(pair, 1);
		} else {
			mStatementMap.put(pair, mStatementMap.get(pair) + 1);
		}
	}
}
