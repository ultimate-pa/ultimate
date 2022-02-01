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

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.function.BinaryOperator;
import java.util.function.Supplier;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.GenericLabeledGraph;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.PathExpressionComputer;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Regex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.RegexToCompactTgf;

public class PathExpressionTest {

	/** Abbreviation for long definition. */
	private static class IntGraph extends GenericLabeledGraph<Integer, String>{
		public IntGraph() {
			super(new LinkedHashSet<>(), new LinkedHashSet<>());
		}
	}

	@Test
	public void simple() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "w", 2);
		IRegex<String> actual = exprBetween(g, 1, 2);
		IRegex<String> expected = Regex.literal("w");
		assertEquals(expected, actual);
	}

	@Test
	public void simple2() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "w", 2);
		g.addEdge(2, "w", 3);
		IRegex<String> actual = exprBetween(g, 1, 3);
		IRegex<String> expected = a("w", "w");
		assertEquals(expected, actual);
	}

	@Test
	public void simple3() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 3);
		g.addEdge(3, "c", 4);
		IRegex<String> actual = exprBetween(g, 1, 4);
		IRegex<String> expected = a("a", "b", "c");
		assertEquals(expected, actual);
	}

	@Test
	public void star2() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 1);
		IRegex<String> actual = exprBetween(g, 1, 2);
		IRegex<String> expected = a("a", star(a("b", "a")));
		assertEquals(expected, actual);
	}

	@Test
	public void star3() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 1);
		g.addEdge(1, "c", 2);
		IRegex<String> actual = exprBetween(g, 1, 2);
		IRegex<String> expected = a(u("c", "a"), star(a("b", u("c", "a"))));
		assertEquals(expected, actual);
	}

	@Test
	public void simple4() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 3);
		g.addEdge(3, "c", 4);
		g.addEdge(1, "c", 4);
		IRegex<String> actual = exprBetween(g, 1, 4);
		IRegex<String> expected = u("c", a("a", "b", "c"));
		assertEquals(expected, actual);
	}

	@Test
	public void star() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 2);
		g.addEdge(2, "c", 3);
		IRegex<String> actual = exprBetween(g, 1, 3);
		IRegex<String> expected = a(a("a", star("b")), "c");
		assertEquals(expected, actual);
	}

	@Test
	public void union() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 3);
		g.addEdge(1, "c", 4);
		g.addEdge(4, "d", 3);
		IRegex<String> actual = exprBetween(g, 1, 3);
		IRegex<String> expected = u(a("a", "b"), a("c", "d"));
		assertEquals(expected, actual);
	}

	@Test
	public void empty() {
		IntGraph g = new IntGraph();
		g.addEdge(2, "a", 1);
		g.addEdge(2, "b", 3);
		g.addEdge(3, "c", 1);
		IRegex<String> actual = exprBetween(g, 1, 3);
		IRegex<String> expected = Regex.emptySet();
		assertEquals(expected, actual);
	}

	@Test
	public void unionAndConcatenate() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(1, "a", 3);
		g.addEdge(2, "b", 4);
		g.addEdge(3, "b", 4);
		g.addEdge(4, "c", 5);
		IRegex<String> actual = exprBetween(g, 1, 5);
		IRegex<String> expected = a("a", "b", "c");
		assertEquals(expected, actual);
	}
	@Test
	public void unionAndConcatenate2() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "b", 4);
		g.addEdge(1, "a", 3);
		g.addEdge(3, "b", 4);
		g.addEdge(4, "c", 5);
		IRegex<String> actual = exprBetween(g, 1, 5);
		IRegex<String> expected = u(a(a("a", "b"), "c"), a("a", a("b", "c")));
		assertEquals(expected, actual);
	}

	@Test
	public void empty2() {
		IntGraph g = new IntGraph();
		g.addEdge(3, "c", 1);
		IRegex<String> actual = exprBetween(g, 1, 3);
		IRegex<String> expected = Regex.emptySet();
		assertEquals(expected, actual);
	}

	@Test
	public void branchWithEps() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "v", 4);
		g.addEdge(1, "c", 3);
		g.addEdge(1, "c", 4);
		IRegex<String> actual = exprBetween(g, 1, 4);
		IRegex<String> expected = u("c", a("a", "v"));
		assertEquals(expected, actual);
	}

	@Test
	public void branchWithEps2() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "a", 2);
		g.addEdge(2, "v", 3);
		g.addEdge(1, "c", 3);
		IRegex<String> actual = exprBetween(g, 1, 3);
		IRegex<String> expected = u("c", a("a", "v"));
		assertEquals(expected, actual);
	}

	@Test
	public void simpleReverse() {
		IntGraph g = new IntGraph();
		g.addEdge(3, "a", 2);
		g.addEdge(2, "v", 1);
		IRegex<String> actual = exprBetween(g, 3, 1);
		IRegex<String> expected = a("a", "v");
		assertEquals(expected, actual);
	}

	@Test
	public void loop() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "12", 2);
		g.addEdge(2, "23", 3);
		g.addEdge(3, "34", 4);
		g.addEdge(4, "43", 3);
		IRegex<String> actual = exprBetween(g, 1, 3);
		IRegex<String> expected = u(a("12", "23"), a(a(a("12", "23", "34"), star(a("43", "34"))), "43"));
		assertEquals(expected, actual);
	}

	@Test
	public void loop2() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "12", 2);
		g.addEdge(2, "21", 1);
		g.addEdge(2, "23", 3);
		g.addEdge(3, "34", 4);
		g.addEdge(4, "43", 3);
		IRegex<String> actual = exprBetween(g, 1, 3);
		IRegex<String> expected = u(a(a("12", star(a("21", "12"))), "23"),
				a(a(a(a(a("12", star(a("21", "12"))), "23"), "34"), star(a("43", "34"))), "43"));
		assertEquals(expected, actual);
	}

	@Test
	public void loop3() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "12", 2);
		g.addEdge(2, "23", 3);
		g.addEdge(3, "32", 2);
		g.addEdge(3, "34", 4);
		g.addEdge(4, "41", 1);
		IRegex<String> actual = exprBetween(g, 1, 1);
		IRegex<String> expected = u(Regex.epsilon(), a(a(a(a(a("12", "23"), star(a("32", "23"))), "34"),
				star(a(a(a("41", "12", "23"), star(a("32", "23"))), "34"))), "41"));
		assertEquals(expected, actual);
	}

	@Test
	public void loop4() {
		IntGraph g = new IntGraph();
		g.addEdge(1, "13", 3);
		g.addEdge(3, "31", 1);
		g.addEdge(3, "34", 4);
		g.addEdge(4, "41", 1);
		IRegex<String> actual = exprBetween(g, 1, 1);
		IRegex<String> expected = u(
				u(Regex.epsilon(),
						a(a(a(a("13", star(a("31", "13"))), "34"),
								star(a(a(a("41", "13"), star(a("31", "13"))), "34"))), "41")),
				a(u(a("13", star(a("31", "13"))),
						a(a(a(a("13", star(a("31", "13"))), "34"),
								star(a(a(a("41", "13"), star(a("31", "13"))), "34"))),
								a(a("41", "13"), star(a("31", "13"))))),
						"31"));
		assertEquals(expected, actual);
	}

	private static IRegex<String> exprBetween(IntGraph graph, int source, int target) {
		return new PathExpressionComputer<>(graph).exprBetween(source, target);
	}
	
	private static IRegex<String> e(String e) {
		return Regex.literal(e);
	}

	private static IRegex<String> a(IRegex<String> a, IRegex<String> b) {
		return Regex.simplifiedConcatenation(a, b);
	}

	private static IRegex<String> a(String a, IRegex<String> b) {
		return a(e(a), b);
	}

	private static IRegex<String> a(IRegex<String> a, String b) {
		return a(a, e(b));
	}

	private static IRegex<String> u(IRegex<String> a, IRegex<String> b) {
		return Regex.simplifiedUnion(a, b);
	}

	private static IRegex<String> u(String a, IRegex<String> b) {
		return u(e(a), b);
	}

	private static IRegex<String> star(IRegex<String> a) {
		return Regex.simplifiedStar(a);
	}

	private static IRegex<String> star(String a) {
		return star(e(a));
	}
	
	private static IRegex<String> a(final String... letters) {
		return pairFromLeft(Regex::epsilon, Regex::concat, letters);
	}
	
	private static IRegex<String> u(final String... letters) {
		return pairFromLeft(Regex::emptySet, Regex::union, letters);
	}

	private static IRegex<String> pairFromLeft(final Supplier<IRegex<String>> neutralElem,
			final BinaryOperator<IRegex<String>> operator, final String... letters) {
		return Arrays.stream(letters).map(Regex::literal).reduce(operator).orElseGet(neutralElem);
	}

	// ----- "Tests" for experimenting with iteration order ---------------------------------------

	//@Test
	public void rersSmallBest() {
		IntGraph g = new IntGraph();
		for (int i = 4; i >= 0; --i) {
			g.addNode(i);
		}
		g.addEdge(0, "a", 1);
		g.addEdge(1, "b", 2);
		g.addEdge(2, "c", 3);
		g.addEdge(3, "d", 0);
		g.addEdge(0, "e", 4);
		g.addEdge(1, "f", 3);
		IRegex<String> actual = exprBetween(g, 0, 4);
		// not a real assert, just there to get output
		assertEquals(RegexToCompactTgf.apply(actual), actual);
	}

	//@Test
	public void rersSmallOk() {
		IntGraph g = new IntGraph();
		for (int i = 0; i <= 4; ++i) {
			g.addNode(i);
		}
		g.addEdge(0, "a", 1);
		g.addEdge(1, "b", 2);
		g.addEdge(2, "c", 3);
		g.addEdge(3, "d", 0);
		g.addEdge(0, "e", 4);
		g.addEdge(1, "f", 3);
		IRegex<String> actual = exprBetween(g, 0, 4);
		// not a real assert, just there to get output
		assertEquals(RegexToCompactTgf.apply(actual), actual);
	}

	//@Test
	public void rersSmallWorst() {
		IntGraph g = new IntGraph();
		g.addNode(0);
		g.addNode(3);
		g.addNode(4);
		g.addNode(1);
		g.addNode(2);
		g.addEdge(3, "d", 0);
		g.addEdge(1, "b", 2);
		g.addEdge(1, "f", 3);
		g.addEdge(0, "a", 1);
		g.addEdge(2, "c", 3);
		g.addEdge(0, "e", 4);
		IRegex<String> actual = exprBetween(g, 0, 4);
		// not a real assert, just there to get output
		assertEquals(RegexToCompactTgf.apply(actual), actual);
	}

	//@Test
	public void dagWorst() {
		IntGraph g = new IntGraph();
		g.addNode(0);
		g.addNode(3);
		g.addNode(4);
		g.addNode(1);
		g.addNode(2);
		g.addEdge(3, "d", 0);
		g.addEdge(1, "b", 2);
		g.addEdge(1, "f", 3);
		g.addEdge(0, "a", 1);
		g.addEdge(2, "c", 3);
		g.addEdge(0, "e", 4);
		g.addEdge(0, "g", 5);
		// not a real assert, just there to get output
		RegexToCompactTgf<String> re2tgf = new RegexToCompactTgf<>();
		exprBetween(g, 0, 4).accept(re2tgf);
		exprBetween(g, 0, 5).accept(re2tgf);
		assertEquals(exprBetween(g, 0, 5), "");
	}

	//@Test
	public void dagBest() {
		IntGraph g = new IntGraph();
		for (int i = 5; i >= 0; --i) {
			g.addNode(i);
		}
		g.addEdge(0, "a", 1);
		g.addEdge(1, "b", 2);
		g.addEdge(2, "c", 3);
		g.addEdge(3, "d", 0);
		g.addEdge(0, "e", 4);
		g.addEdge(1, "f", 3);
		g.addEdge(0, "g", 5);
		// not a real assert, just there to get output
		RegexToCompactTgf<String> re2tgf = new RegexToCompactTgf<>();
		exprBetween(g, 0, 4).accept(re2tgf);
		exprBetween(g, 0, 5).accept(re2tgf);
		assertEquals(exprBetween(g, 0, 5), "");
	}
}
