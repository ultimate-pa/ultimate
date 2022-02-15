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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.independencerelation;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IndependenceStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * A simple and efficient syntax-based independence relation. Two actions are independent if all variable accessed by
 * both of them are only read, not written to.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            This relation is non-conditional, so this parameter is not used.
 * @param <L>
 *            The type of letters whose independence is tracked
 */
public class SyntacticIndependenceRelation<STATE, L extends IAction> implements IIndependenceRelation<STATE, L> {
	private final IndependenceStatisticsDataProvider mStatistics;

	public SyntacticIndependenceRelation(final IToolchainStorage storage) {
		mStatistics = new IndependenceStatisticsDataProvider(storage, SyntacticIndependenceRelation.class);
	}

	@Override
	public boolean isSymmetric() {
		return true;
	}

	@Override
	public boolean isConditional() {
		return false;
	}

	@Override
	public boolean contains(final STATE state, final L a, final L b) {
		final TransFormula tf1 = a.getTransformula();
		final TransFormula tf2 = b.getTransformula();

		final boolean noWWConflict =
				DataStructureUtils.haveEmptyIntersection(tf1.getAssignedVars(), tf2.getAssignedVars());
		final boolean noWRConflict =
				DataStructureUtils.haveEmptyIntersection(tf1.getAssignedVars(), tf2.getInVars().keySet());
		final boolean noRWConflict =
				DataStructureUtils.haveEmptyIntersection(tf1.getInVars().keySet(), tf2.getAssignedVars());

		final boolean result = noWWConflict && noWRConflict && noRWConflict;
		mStatistics.reportQuery(result, false);
		return result;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}
}
