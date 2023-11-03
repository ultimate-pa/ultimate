/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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

import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IndependenceStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;

/**
 * An independence relation that can be used as a wrapper around conditional instances of
 * {@link SemanticIndependenceRelation}. It eliminates useless conditions, leading to simpler SMT queries. If the
 * results of the {@link SemanticIndependenceRelation} are cached, this wrapper should instead wrap the
 * {@link CachedIndependenceRelation}, in order to also improve caching efficiency.
 *
 * A condition is deemed useless for the independence of statements a and b, if the condition is consistent
 * (satisfiable), but does not contain any free variable that is read by either a or b.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters being cached.
 */
public final class SemanticConditionEliminator<L extends IAction> implements IIndependenceRelation<IPredicate, L> {

	private final IIndependenceRelation<IPredicate, L> mUnderlying;
	private final Predicate<IPredicate> mIsInconsistent;
	private final EliminatorStatistics mStatistics;

	/**
	 * Creates a new wrapper around a given independence relation.
	 *
	 * @param underlying
	 *            The underlying independence relation to which queries will be delegated (after possibly eliminating
	 *            the condition). This relation should be able to handle null as condition.
	 * @param isInconsistent
	 *            An inconsistency test to be used for conditions given to this relation. To truly gain efficiency, this
	 *            test should be very efficient. It must return true for all inconsistent conditions this relation is
	 *            used on, in order to ensure soundness. It may over-approximate inconsistency, i.e., also return true
	 *            for some consistent predicates -- this affects efficiency but not soundness.
	 */
	public SemanticConditionEliminator(final IIndependenceRelation<IPredicate, L> underlying,
			final Predicate<IPredicate> isInconsistent) {
		assert underlying.isConditional() : "Condition elimination for non-conditional relations is useless";
		mUnderlying = underlying;
		mIsInconsistent = isInconsistent;
		mStatistics = new EliminatorStatistics();
	}

	@Override
	public boolean isSymmetric() {
		return mUnderlying.isSymmetric();
	}

	@Override
	public boolean isConditional() {
		return mUnderlying.isConditional();
	}

	@Override
	public Dependence isIndependent(final IPredicate state, final L a, final L b) {
		final IPredicate condition = state == null ? null : normalize(state, a, b);
		final Dependence result = mUnderlying.isIndependent(condition, a, b);
		mStatistics.reportQuery(result, condition != null);
		return result;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private IPredicate normalize(final IPredicate condition, final L a, final L b) {
		// Syntactically determine if condition is possibly relevant to independence.
		if (mIsInconsistent.test(condition) || isRelevant(condition, a) || isRelevant(condition, b)) {
			return condition;
		}

		// If condition irrelevant, fall back to independence without condition.
		mStatistics.reportEliminatedCondition();
		return null;
	}

	private boolean isRelevant(final IPredicate condition, final L statement) {
		return DataStructureUtils.haveNonEmptyIntersection(condition.getVars(),
				statement.getTransformula().getInVars().keySet());
	}

	private class EliminatorStatistics extends IndependenceStatisticsDataProvider {
		public static final String ELIMINATED_CONDITIONS = "Eliminated conditions";

		private int mEliminatedConditions;

		public EliminatorStatistics() {
			super(SemanticConditionEliminator.class, mUnderlying);
			declare(ELIMINATED_CONDITIONS, () -> mEliminatedConditions, KeyType.COUNTER);
		}

		private void reportEliminatedCondition() {
			mEliminatedConditions++;
		}
	}
}
