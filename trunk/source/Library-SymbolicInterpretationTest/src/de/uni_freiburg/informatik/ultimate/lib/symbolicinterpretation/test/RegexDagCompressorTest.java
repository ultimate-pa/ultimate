/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.test;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Regex;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDag;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDagCompressor;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDagNode;

public class RegexDagCompressorTest {

	@Test
	public void justOneEpsilon() {
		compressAssertEq("0ε", "", linearDag(""));
	}

	@Test
	public void justTwoEpsilon() {
		compressAssertEq("0ε", "", linearDag("", ""));
	}

	@Test
	public void epsilonSourceAndSink() {
		compressAssertEq("0a", "", linearDag("", "a", ""));
	}

	@Test
	public void chainOfEpsilons() {
		compressAssertEq("0a 1b 2c", "01 12", linearDag("a", "", "", "b", "", "", "", "c"));
		compressAssertEq("0a 1b 2c", "01 12", linearDag("", "", "a", "b", "c", "", "", ""));
	}

	@Test
	public void unmergeableChain() {
		compressAssertEq("0a 1b 2c", "01 12", linearDag("a", "b", "c"));
		compressAssertEq("0a 1a 2a", "01 12", linearDag("a", "a", "a"));
	}

	// TODO more tests, especially for non-linear DAGs
	// ==> generate DAG from simplified TGF string

	private static RegexDag<String> linearDag(final String source, final String... successors) {
		final RegexDag<String> dag = new RegexDag<>(stringToRegexLiteral(source));
		for (final String next : successors) {
			RegexDagNode<String> nextNode = new RegexDagNode<>(stringToRegexLiteral(next));
			dag.getSink().connectOutgoing(nextNode);
			dag.setSink(nextNode);
		}
		return dag;
	}

	private static IRegex<String> stringToRegexLiteral(final String letter) {
		if (letter.isEmpty()) {
			return Regex.epsilon();
		}
		return Regex.literal(letter);
	}

	private static String toLongTgf(final String tgfNodesExpected, final String tgfEdgesExpected) {
		return tgfNodesExpected.replaceAll("(\\d+)([^\\d ]+) *", "$1 $2\n")
				+ "#\n"
				+ tgfEdgesExpected.replaceAll("(\\d+)\\.?(\\d+) *", "$1 $2 forward\n$2 $1 backward\n");
	}

	private static void compressAssertEq(final String tgfNodesExpected, final String tgfEdgesExpected,
			final RegexDag<String> dag) {
		assertEq(tgfNodesExpected, tgfEdgesExpected, new RegexDagCompressor<String>().compress(dag));
	}

	private static void assertEq(final String tgfNodesExpected, final String tgfEdgesExpected,
			final RegexDag<String> actualDag) {
		// leading \n makes jUnit output ("expected <...> but was <...>") more readable
		Assert.assertEquals("\n" + toLongTgf(tgfNodesExpected, tgfEdgesExpected), "\n" + actualDag.toString());
	}

}
