/*
 * Copyright (C) 2026 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.MusEnumerator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.MusEnumerator.MusEnumeratorResult;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class MusEnumeratorTest {
	private Script mScriptSubsetSolver;
	private Script mScriptMapSolver;

	@Before
	public void setUp() {
		mScriptSubsetSolver = UltimateMocks.createZ3Script();
		mScriptSubsetSolver.setOption(SMTLIBConstants.PRODUCE_UNSAT_CORES, "true");

		mScriptMapSolver = UltimateMocks.createZ3Script();
		mScriptMapSolver.setOption(SMTLIBConstants.PRODUCE_MODELS, "true");
		mScriptMapSolver.setLogic(Logics.ALL);
	}

	@Test
	public void testEnumerate() {
		mScriptSubsetSolver.setLogic(Logics.QF_LRA);

		final Sort realSort = mScriptSubsetSolver.getTheory().getRealSort();
		mScriptSubsetSolver.declareFun("x", new Sort[0], realSort);
		mScriptSubsetSolver.declareFun("y", new Sort[0], realSort);
		final Term x = mScriptSubsetSolver.term("x");
		final Term y = mScriptSubsetSolver.term("y");

		final Term zero = mScriptSubsetSolver.numeral("0");
		final Term one = mScriptSubsetSolver.numeral("1");
		final Term two = mScriptSubsetSolver.numeral("2");

		final List<Term> constraints = new ArrayList<>() {
			{
				// 0: x > 2
				add(SmtUtils.greater(mScriptSubsetSolver, x, two));
				// 1: x < 1
				add(SmtUtils.less(mScriptSubsetSolver, x, one));
				// 2: x < 0
				add(SmtUtils.less(mScriptSubsetSolver, x, zero));
				// 3: Or(x + y > 0, y < 0)
				add(SmtUtils.or(mScriptSubsetSolver,
						SmtUtils.greater(mScriptSubsetSolver, SmtUtils.sum(mScriptSubsetSolver, "+", x, y), zero),
						SmtUtils.less(mScriptSubsetSolver, y, zero)));
				// 4: Or(y >= 0, x >= 0)
				add(SmtUtils.or(mScriptSubsetSolver, SmtUtils.geq(mScriptSubsetSolver, y, zero),
						SmtUtils.geq(mScriptSubsetSolver, x, zero)));
				// 5: Or(y < 0, x < 0)
				add(SmtUtils.or(mScriptSubsetSolver, SmtUtils.less(mScriptSubsetSolver, y, zero),
						SmtUtils.less(mScriptSubsetSolver, x, zero)));
				// 6: Or(y > 0, x < 0)
				add(SmtUtils.or(mScriptSubsetSolver, SmtUtils.greater(mScriptSubsetSolver, y, zero),
						SmtUtils.less(mScriptSubsetSolver, x, zero)));
			}
		};

		final Set<MusEnumeratorResult> expected = Set.of(
				// MUS: {0, 2}, [x > 2, x < 0]
				new MusEnumeratorResult(MusEnumeratorResult.Type.MUS, Set.of(0, 2),
						List.of(constraints.get(0), constraints.get(2))),
				// MUS: {0, 5, 6}, [x > 2, Or(y < 0, x < 0), 6: Or(y > 0, x < 0)]
				new MusEnumeratorResult(MusEnumeratorResult.Type.MUS, Set.of(0, 5, 6),
						List.of(constraints.get(0), constraints.get(5), constraints.get(6))),
				// MSS: {1, 2, 3, 4, 5, 6},
				// [x < 1, x < 0, Or(x + y > 0, y < 0), Or(y >= 0, x >= 0), Or(y < 0, x < 0), Or(y > 0, x < 0)]
				new MusEnumeratorResult(MusEnumeratorResult.Type.MSS, Set.of(1, 2, 3, 4, 5, 6),
						List.of(constraints.get(1), constraints.get(2), constraints.get(3), constraints.get(4),
								constraints.get(5), constraints.get(6))),
				// MUS: {0, 1}, [x > 2, x < 1]
				new MusEnumeratorResult(MusEnumeratorResult.Type.MUS, Set.of(0, 1),
						List.of(constraints.get(0), constraints.get(1))),
				// MSS: {0, 3, 4, 6}, [x > 2, Or(x + y > 0, y < 0), Or(y >= 0, x >= 0), Or(y > 0, x < 0)]
				new MusEnumeratorResult(MusEnumeratorResult.Type.MSS, Set.of(0, 3, 4, 6),
						List.of(constraints.get(0), constraints.get(3), constraints.get(4), constraints.get(6))),
				// MSS: {0, 3, 4, 5}, [x > 2, Or(x + y > 0, y < 0), Or(y >= 0, x >= 0), Or(y < 0, x < 0)]
				new MusEnumeratorResult(MusEnumeratorResult.Type.MSS, Set.of(0, 3, 4, 5),
						List.of(constraints.get(0), constraints.get(3), constraints.get(4), constraints.get(5))));

		final Set<MusEnumeratorResult> actual =
				new HashSet<>(MusEnumerator.enumerate(mScriptSubsetSolver, mScriptMapSolver, constraints, null));

		assert expected.equals(actual) : "Expected: " + expected + ", but got: " + actual;
	}
}
