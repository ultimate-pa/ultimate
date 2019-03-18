/*
 * Code taken from https://github.com/johspaeth/PathExpression
 * Copyright (C) 2018 Johannes Spaeth
 * Copyright (C) 2018 Fraunhofer IEM, Paderborn, Germany
 * 
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-PathExpressions plug-in.
 *
 * The ULTIMATE Library-PathExpressions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-PathExpressions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-PathExpressions plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-PathExpressions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-PathExpressions plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.pathexpressions.test;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.PathExpressionComputer;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Concatenate;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.EmptySet;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Plain;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Regex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Union;

public class PathExpressionTest {
	@Test
	public void simple() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "w", 2);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 2);
		IRegex<String> expected = new Plain<>("w");
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void simple2() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "w", 2);
		g.addEdge(2, "w", 3);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 3);
		IRegex<String> expected = a("w", "w");
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void simple3() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 3);
		g.addEdge(3, "c", 4);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 4);
		IRegex<String> expected = a(a("a", "b"), "c");
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void star2() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 1);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 2);
		IRegex<String> expected = a("a", star(a("b", "a")));
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void star3() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 1);
		g.addEdge(1, "c", 2);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 2);
		IRegex<String> expected = a(u("c", "a"), star(a("b", u("c", "a"))));
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void simple4() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 3);
		g.addEdge(3, "c", 4);
		g.addEdge(1, "c", 4);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 4);
		IRegex<String> expected = u("c", a(a("a", "b"), "c"));
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void star() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 2);
		g.addEdge(2, "c", 3);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 3);
		IRegex<String> expected = a(a("a", star("b")), "c");
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void union() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 3);
		g.addEdge(1, "c", 4);
		g.addEdge(4, "d", 3);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 3);
		IRegex<String> expected = u(a("a", "b"), a("c", "d"));
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void empty() {
		IntGraph g = new IntGraph();
		g.addEdge(2, "a", 1);
		g.addEdge(2, "b", 3);
		g.addEdge(3, "c", 1);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 3);
		IRegex<String> expected = new EmptySet<>();
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void unionAndConcatenate() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 4);
		g.addEdge(1, "a", 3);
		g.addEdge(3, "b", 4);
		g.addEdge(4, "c", 5);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 5);
		IRegex<String> expected = a(a("a", "b"), "c");
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void empty2() {
		IntGraph g = new IntGraph();
		g.addEdge(3, "c", 1);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 3);
		IRegex<String> expected = new EmptySet<>();
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void branchWithEps() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "v", 4);
		g.addEdge(1, "c", 3);
		g.addEdge(1, "c", 4);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 4);
		IRegex<String> expected = u("c", a("a", "v"));
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void branchWithEps2() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "v", 3);
		g.addEdge(1, "c", 3);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 3);
		IRegex<String> expected = u("c", a("a", "v"));
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void simpleReverse() {
		IntGraph g = new IntGraph();
		g.addEdge(3, "a", 2);
		g.addEdge(2, "v", 1);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(3, 1);
		IRegex<String> expected = a("a", "v");
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void loop() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "12", 2);
		g.addEdge(2, "23", 3);
		g.addEdge(3, "34", 4);
		g.addEdge(4, "43", 3);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 3);
		IRegex<String> expected = u(a("12", "23"), a(a(a(a("12", "23"), "34"), star(a("43", "34"))), "43"));
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void loop2() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "12", 2);
		g.addEdge(2, "21", 1);
		g.addEdge(2, "23", 3);
		g.addEdge(3, "34", 4);
		g.addEdge(4, "43", 3);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 3);
		IRegex<String> expected = u(a(a("12", star(a("21", "12"))), "23"),
				a(a(a(a(a("12", star(a("21", "12"))), "23"), "34"), star(a("43", "34"))), "43"));
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void loop3() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "12", 2);
		g.addEdge(2, "23", 3);
		g.addEdge(3, "32", 2);
		g.addEdge(3, "34", 4);
		g.addEdge(4, "41", 1);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 1);
		IRegex<String> expected = u(new Epsilon<>(), a(a(a(a(a("12", "23"), star(a("32", "23"))), "34"),
				star(a(a(a(a("41", "12"), "23"), star(a("32", "23"))), "34"))), "41"));
		assertEquals(expected, expressionBetween);
	}

	@Test
	public void loop4() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "13", 3);
		g.addEdge(3, "31", 1);
		g.addEdge(3, "34", 4);
		g.addEdge(4, "41", 1);
		PathExpressionComputer<Integer, String> expr = new PathExpressionComputer<>(g);
		IRegex<String> expressionBetween = expr.getExpressionBetween(1, 1);
		IRegex<String> expected = u(
				u(new Epsilon<>(), a(a(a(a("13", star(a("31", "13"))), "34"), star(a(a(a("41", "13"), star(a("31", "13"))), "34"))), "41")),
				a(u(a("13", star(a("31", "13"))),
						a(a(a(a("13", star(a("31", "13"))), "34"),
								star(a(a(a("41", "13"), star(a("31", "13"))), "34"))),
								a(a("41", "13"), star(a("31", "13"))))),
						"31"));
		assertEquals(expected, expressionBetween);
	}

	private static IRegex<String> e(String e) {
		return new Plain<>(e);
	}

	private static IRegex<String> a(IRegex<String> a, IRegex<String> b) {
		return Regex.<String>simplifiedConcatenation(a, b);
	}

	private static IRegex<String> a(String a, IRegex<String> b) {
		return a(e(a), b);
	}

	private static IRegex<String> a(IRegex<String> a, String b) {
		return a(a, e(b));
	}

	private static IRegex<String> a(String a, String b) {
		return a(e(a), e(b));
	}

	private static IRegex<String> u(IRegex<String> a, IRegex<String> b) {
		return Regex.<String>simplifiedUnion(a, b);
	}

	private static IRegex<String> u(String a, String b) {
		return u(e(a), e(b));
	}

	private static IRegex<String> u(IRegex<String> a, String b) {
		return u(a, e(b));
	}

	private static IRegex<String> u(String a, IRegex<String> b) {
		return u(e(a), b);
	}

	private static IRegex<String> star(IRegex<String> a) {
		return Regex.<String>simplifiedStar(a);
	}

	private static IRegex<String> star(String a) {
		return star(e(a));
	}

	private static String toTestString(IRegex<String> regEx) {
		if (regEx instanceof EmptySet) {
			return "";
		} else if (regEx instanceof Plain) {
			return String.format("\"%s\"", ((Plain) regEx).getV());
		} else if (regEx instanceof Concatenate) {
			Concatenate concat = (Concatenate) regEx;
			return String.format("a(%s, %s)", toTestString(concat.getFirst()), toTestString(concat.getSecond()));
		} else if (regEx instanceof Union) {
			Union union = (Union) regEx;
			return String.format("u(%s, %s)", toTestString(union.getFirst()), toTestString(union.getSecond()));
		} else if (regEx instanceof Star) {
			return String.format("star(%s)", toTestString(((Star) regEx).getPlain()));
		} else {
			throw new IllegalArgumentException("Unhandled regex: " + regEx);
		}
	}

}
