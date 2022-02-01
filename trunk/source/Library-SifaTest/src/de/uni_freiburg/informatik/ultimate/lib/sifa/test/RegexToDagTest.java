/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Regex;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexToDag;

public class RegexToDagTest {

	@Test
	public void testEpsilon() {
		assertEq("0ε 1ε", "01", ε);
	}

	@Test
	public void testLiteral() {
		assertEq("0ε 1a 2ε", "01 12", l("a"));
	}

	@Test
	public void testConcat() {
		assertEq("0ε 1a 2b 3ε", "01 12 23", c(l("a"), l("b")));
	}

	@Test
	public void testUnion() {
		assertEq("0ε 1a 2b 3ε 4ε", "01 02 13 23 34", u(l("a"), l("b")));
	}

	@SafeVarargs
	public static void assertEq(final String nodesExpected, final String edgesExpected,
			final IRegex<String>... regexesToBeAdded) {
		RegexToDag<String> re2dag = new RegexToDag<>();
		for (final IRegex<String> re : regexesToBeAdded) {
			re2dag.add(re);
		}
		RegexDagTestUtils.assertEq(nodesExpected, edgesExpected, re2dag.getDagAndReset());
	}

	private static final IRegex<String> ε = Regex.epsilon();

	/** Concats two regexes. The c stands for concat. */
	private static IRegex<String> c(final IRegex<String> left, final IRegex<String> right) {
		return Regex.concat(left, right);
	}

	/** Unions two regexes. The u stands for union and looks like the union operator “∪”. */
	private static IRegex<String> u(final IRegex<String> left, final IRegex<String> right) {
		return Regex.union(left, right);
	}

	/** Creates a regex literal. The l stands for literal.*/
	private static IRegex<String> l(final String letter) {
		return Regex.literal(letter);
	}
}
