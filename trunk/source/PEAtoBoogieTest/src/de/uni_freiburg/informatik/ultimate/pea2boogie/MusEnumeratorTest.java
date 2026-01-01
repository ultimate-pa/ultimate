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
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.MusEnumerator.MapSolver;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.MusEnumerator.MusEnumeratorResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.MusEnumerator.SubsetSolver;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class MusEnumeratorTest {
	private Script mScriptCSolver;
	private Script mScriptMSolver;

	@Before
	public void setUp() {
		mScriptCSolver = UltimateMocks.createZ3Script();
		mScriptCSolver.setOption(SMTLIBConstants.PRODUCE_UNSAT_CORES, "true");

		mScriptMSolver = UltimateMocks.createZ3Script();
		mScriptCSolver.setOption(SMTLIBConstants.PRODUCE_MODELS, "true");
		mScriptMSolver.setLogic(Logics.ALL);
	}

	@Test
	public void testEnumerate() {
		mScriptCSolver.setLogic(Logics.QF_LRA);

		final Sort realSort = mScriptCSolver.getTheory().getRealSort();
		mScriptCSolver.declareFun("x", new Sort[0], realSort);
		mScriptCSolver.declareFun("y", new Sort[0], realSort);
		final Term x = mScriptCSolver.term("x");
		final Term y = mScriptCSolver.term("y");

		final Term zero = mScriptCSolver.numeral("0");
		final Term one = mScriptCSolver.numeral("1");
		final Term two = mScriptCSolver.numeral("2");

		final List<Term> constraints = new ArrayList<>() {
			{
				// 0: x > 2
				add(SmtUtils.greater(mScriptCSolver, x, two));
				// 1: x < 1
				add(SmtUtils.less(mScriptCSolver, x, one));
				// 2: x < 0
				add(SmtUtils.less(mScriptCSolver, x, zero));
				// 3: Or(x + y > 0, y < 0)
				add(SmtUtils.or(mScriptCSolver,
						SmtUtils.greater(mScriptCSolver, SmtUtils.sum(mScriptCSolver, "+", x, y), zero),
						SmtUtils.less(mScriptCSolver, y, zero)));
				// 4: Or(y >= 0, x >= 0)
				add(SmtUtils.or(mScriptCSolver, SmtUtils.geq(mScriptCSolver, y, zero),
						SmtUtils.geq(mScriptCSolver, x, zero)));
				// 5: Or(y < 0, x < 0)
				add(SmtUtils.or(mScriptCSolver, SmtUtils.less(mScriptCSolver, y, zero),
						SmtUtils.less(mScriptCSolver, x, zero)));
				// 6: Or(y > 0, x < 0)
				add(SmtUtils.or(mScriptCSolver, SmtUtils.greater(mScriptCSolver, y, zero),
						SmtUtils.less(mScriptCSolver, x, zero)));
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

		final SubsetSolver cSolver = new SubsetSolver(mScriptCSolver, constraints);
		final MapSolver mSolver = new MapSolver(mScriptMSolver, constraints.size());

		final Set<MusEnumeratorResult> actual = new HashSet<>(MusEnumerator.enumerate(cSolver, mSolver, null));

		assert expected.equals(actual) : "Expected: " + expected + ", but got: " + actual;
	}
}
