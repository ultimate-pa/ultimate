/*
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IndependenceStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * A simple and efficient syntax-based independence relation. Two actions are independent if all variable accessed by
 * both of them are only read, not written to.
 *
 * An extension of this basic idea allows statements to commute if the only conflicts between them are write/write
 * conflicts and both statements havoc the affected variables.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            This relation is non-conditional, so this parameter is not used.
 * @param <L>
 *            The type of letters whose independence is tracked
 */
public class SyntacticIndependenceRelation<STATE, L extends IAction> implements IIndependenceRelation<STATE, L> {

	private static final boolean ALLOW_MUTUAL_HAVOCS = true;

	private final IndependenceStatisticsDataProvider mStatistics =
			new IndependenceStatisticsDataProvider(SyntacticIndependenceRelation.class);

	@Override
	public boolean isSymmetric() {
		return true;
	}

	@Override
	public boolean isConditional() {
		return false;
	}

	@Override
	public Dependence isIndependent(final STATE state, final L a, final L b) {
		final TransFormula tf1 = a.getTransformula();
		final TransFormula tf2 = b.getTransformula();

		if (DataStructureUtils.haveNonEmptyIntersection(tf1.getAssignedVars(), tf2.getInVars().keySet())) {
			// write-read conflict
			mStatistics.reportDependentQuery(false);
			return Dependence.DEPENDENT;
		}

		if (DataStructureUtils.haveNonEmptyIntersection(tf1.getInVars().keySet(), tf2.getAssignedVars())) {
			// read-write conflict
			mStatistics.reportDependentQuery(false);
			return Dependence.DEPENDENT;
		}

		final boolean wwConflict;
		if (ALLOW_MUTUAL_HAVOCS) {
			wwConflict = DataStructureUtils.intersection(tf1.getAssignedVars(), tf2.getAssignedVars()).stream()
					.anyMatch(x -> !tf1.isHavocedOut(x) || !tf2.isHavocedOut(x));
		} else {
			wwConflict = DataStructureUtils.haveNonEmptyIntersection(tf1.getAssignedVars(), tf2.getAssignedVars());
		}
		if (wwConflict) {
			mStatistics.reportDependentQuery(false);
			return Dependence.DEPENDENT;
		}

		mStatistics.reportIndependentQuery(false);
		return Dependence.INDEPENDENT;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}
}
