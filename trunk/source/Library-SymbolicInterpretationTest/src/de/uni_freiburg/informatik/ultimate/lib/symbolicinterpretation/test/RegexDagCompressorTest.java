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

import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDag;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDagCompressor;
import static de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.test.RegexDagTestUtils.*;

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

	@Test
	public void simpleDiamond() {
		final String edges = "01 02 13 23";
		compressAssertEq("0a 1b 2c", "01 12", dag("0a 1b 2b 3c", edges));
		compressAssertEq("0b 1c", "01", dag("0ε 1b 2b 3c", edges));
	}

	@Test
	public void multiMergeDiamond() {
		compressAssertEq("0a 1d 2b 3c 4e", "01 02 03 14 24 34",
				dag("0a 1b 2c 3c 4d 5b 6e", "01 02 03 04 05 16 26 36 46 56"));
	}

	@Test
	public void mergeForkOnly() {
		// TODO
		// Without changes suddenly failed unexpectedly on monteverdi but not my system, see
		// https://monteverdi.informatik.uni-freiburg.de/ci/job/Ultimate%20Nightly/2121/
		// could reproduce once, fixed, worked after fix, failed after removing inputsOfNonReproducalbeTestFails
		compressAssertEq("0a 1b 2c 3d", "01 13 12 23",
				dag("0a 1b 2b 3c 4d", "01 13 34 02 24"));
	}

	@Test
	public void mergeJoinOnly() {
		compressAssertEq("0a 1b 2c 3d", "01 12 02 23",
				dag("0a 1b 2c 3c 4d", "01 13 34 02 24"));
	}

	@Test
	public void unmergeableEpsilon() {
		final String nodes = "0ε 1a 2b 3c";
		final String edges = "01 02 13 23";
		compressAssertEq(nodes, edges, dag(nodes, edges));
	}

	@Test
	public void example1() {
		// TODO
		// Without changes suddenly failed unexpectedly on monteverdi but not my system, see
		// https://monteverdi.informatik.uni-freiburg.de/ci/job/Ultimate%20Nightly/2121/
		// could reproduce once, but after fixing mergeForkOnly could no longer reproduce
		compressAssertEq("0ε 1a 2e 3b 4c 5f 6a", "01 02 13 34 35 42 46 52 65",
				dag("14ε 1e 2a 3b 4c 5e 6a 7b 8c 9a 10f 11e 12b 13a 0ε",
				"10 23 50 67 11.0 12.10 13.12 34 78 45 89 10.11 9.10 14.2 14.13 14.6 14.1"));
	}

	@Test
	public void inputsOfNonReproducalbeTestFails() {
		// mergeJoinOnly
		assertParsingDagEqualsTgf("0a 1b 2c 3c 4d", "01 13 34 02 24");
		// example1
		assertParsingDagEqualsTgf("0ε 1a 2e 3b 4c 5f 6a", "01 02 13 34 35 42 46 52 65");
	}

	private static void assertParsingDagEqualsTgf(final String nodes, final String edges) {
		Assert.assertEquals(
				sortTgf(dag(nodes, edges).toString()),
				sortTgf(toTgf(nodes, edges)));
	}

	// TODO create some test cases including ∅

	private static void compressAssertEq(final String nodesExpected, final String edgesExpected,
			final RegexDag<String> dag) {
		assertEq(nodesExpected, edgesExpected, new RegexDagCompressor<String>().compress(dag));
	}

	private static void assertEq(final String nodesExpected, final String edgesExpected,
			final RegexDag<String> actualDag) {
		// Assert is very fragile:
		// Usually we had to check graph isomorphism, which is complicated.
		// We compare the trivial graph format (TGF) representation which is faster but unreliable.
		// TGFs can differ for isomorph graph because of different node ids
		// A benefit of comparing TGFs is human-readable output for failed asserts.

		// leading \n makes jUnit's output ("expected <...> but was <...>") more readable
		Assert.assertEquals(
				"\n" + sortTgf(toTgf(nodesExpected, edgesExpected)),
				"\n" + sortTgf(actualDag.toString()));
		// TODO assert source and sink nodes are set correctly
	}

}
