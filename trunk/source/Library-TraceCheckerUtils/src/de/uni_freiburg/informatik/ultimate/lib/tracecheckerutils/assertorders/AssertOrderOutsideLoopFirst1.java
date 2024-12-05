/*
 * Copyright (C) 2014-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the
 * ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE TraceCheckerUtils Library,
 * or any covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE TraceCheckerUtils Library grant you additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;

/**
 * First, assert all statements which don't occur inside of a loop. Then, check for satisfiability. If the result of the
 * satisfiability check is not unsatisfiable, then assert the rest of the statements, and return the result of the
 * unsatisfiability check.
 *
 * @author Betim Musa (musab@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class AssertOrderOutsideLoopFirst1<L extends IAction> implements IAssertOrder<L> {
	@Override
	public List<Set<Integer>> partition(final Counterexample<L> counterexample) {
		final Map<Integer, Set<Integer>> depth2Statements =
				AssertOrderUtils.partitionStatementsAccordingDepth(counterexample);
		// Statements outside of a loop have depth 0.
		// First, annotate and assert the statements, which doesn't occur within a loop
		final Set<Integer> stmtsOutsideOfLoop = depth2Statements.get(0);
		if (stmtsOutsideOfLoop.size() == counterexample.getWord().length()) {
			return List.of(stmtsOutsideOfLoop);
		}
		// Then assert the other statements.
		final Set<Integer> stmtsWithinLoop =
				AssertOrderUtils.getTraceDifference(counterexample.getWord(), stmtsOutsideOfLoop);
		return List.of(stmtsOutsideOfLoop, stmtsWithinLoop);
	}
}
