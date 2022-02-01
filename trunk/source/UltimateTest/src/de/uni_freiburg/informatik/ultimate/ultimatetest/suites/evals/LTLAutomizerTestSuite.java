/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Test Library.
 *
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Test Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.evals;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.LTLCheckerTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;

public class LTLAutomizerTestSuite extends AbstractEvalTestSuite {

	private static final String[] FILEENDINGS = new String[] { ".c" };

	// @formatter:off
	private static final String[] TOOLCHAINS = new String[] {
			"LTLAutomizerC.xml",
			// "LTLAutomizerCInline.xml",
	};

	private static final String[] SETTINGS = new String[] {
			// Note: SBE is currently broken

			// no optimizations
//			"None.epf",

			// only small and large block encoding
//			"None+SBE.epf",
//			"None+SBE+SASBE.epf",
//			"None+LBE-Multi.epf",

			// only local optimizations (sink states, final states, locally infeasible edges)
			"Default.epf",
			"Default-z3.epf",

			// small block encoding + local optimizations
//			"Default+SBE.epf",
//			"Default+SBE+SASBE.epf",

			// large block encoding + local optimizations
			"Default-LBE-Multi.epf",
//			"Default-LBE-Multi+IB.epf",
//			"Default-LBE-Single.epf",
//			"Default-LBE-SNME.epf",

			// different solver modes
//			"Default-LBE-Multi-z3.epf",
//			"Default-LBE-Multi-z3interpol.epf",

			// different buchi automata constructions
//			"Default-LBE-Multi+NondetBuchi.epf",

			// nearly all optimizations
//			"Default-LBE-Multi+SBE.epf",
//			"Default-LBE-Multi+SBE+IB.epf",
//			"Default-LBE-Multi+SBE+SASBE.epf",
//			"Default-LBE-Multi+SBE+SASBE+IB.epf",
//
	};

	private static final DirectoryFileEndingsPair[] INPUT = new DirectoryFileEndingsPair[] {
			// getPair("examples/LTL/rers2012/P14/", 1),
			// getPair("examples/LTL/rers2012/P15/", 1),
			// getPair("examples/LTL/rers2012/P16/", 1),
			// getPair("examples/LTL/rers2012/P17/", 1),
			// getPair("examples/LTL/rers2012/P18/", 1),
			// getPair("examples/LTL/rers2012/P19/", 1),

//			 getPair("examples/LTL/rers2012correctencoding/P15/"),
//			 getPair("examples/LTL/rers2012correctencoding/P16/"),
//			 getPair("examples/LTL/rers2012correctencoding/P17/"),
//			 getPair("examples/LTL/rers2012correctencoding/P18/"),
//			 getPair("examples/LTL/rers2012correctencoding/P19/"),
//			 getPair("examples/LTL/rers2012correctencoding/P14/"),

			getPair("examples/LTL/coolant/"),
			getPair("examples/LTL/koskinen/ltlcmodelchecker-benchmarks/"),
			getPair("examples/LTL/bugs/"),
			getPair("examples/LTL/simple/"),

			// Possible soundness bug
//			getPair("examples/LTL/koskinen/ltlcmodelchecker-benchmarks/18-windows_os_frag4_prop2.c"),
//			getPair("examples/LTL/rers2012/P14/Problem14_prop_003.c"),

	};
	// @formatter:on

	@Override
	protected long getTimeout() {
		// return 180 * 1000;
		return 15 * 60 * 1000;
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		// @formatter:off
		return new ColumnDefinition[]{
				new ColumnDefinition(
						"Runtime (ns)", "Total time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Allocated memory end (bytes)", "Alloc. Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
				new ColumnDefinition(
						"Peak memory consumption (bytes)", "Peak Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),

				new ColumnDefinition(
						"Overall iterations", "Iterations",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Overall time", "BA analysis time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Minimization time", "BA minimization time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),

				new ColumnDefinition(
						"Initial property automaton Locations", "Initial property automaton Locations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Initial property automaton Edges", "Initial property automaton Edges",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Initial RCFG Locations", "Initial RCFG Locations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Initial RCFG Edges", "Initial RCFG Edges",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Initial product Locations", "Initial product Locations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Initial product Edges", "Initial product Edges",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Optimized Product Locations", "Optimized Product Locations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(
						"Optimized Product Edges", "Optimized Product Edges",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),

				new ColumnDefinition(
						"Trivial modules", "Trivial modules",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Deterministic modules", "Deterministic modules",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Nondeterministic modules", "Nondeterministic modules",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Remainer module", "Remainder",
						ConversionContext.Keep(), Aggregate.Ignore, Aggregate.Ignore),
				new ColumnDefinition(
						"Avg Locs trivial modules", "Avg Locs trivial modules",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Avg Locs deterministic modules", "Avg Locs deterministic modules",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(
						"Avg Locs nondeterministic modules", "Avg Locs nondeterministic modules",
						ConversionContext.BestFitNumber(), Aggregate.Sum, Aggregate.Average),
			};
		// @formatter:on
	}

	@Override
	public ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new LTLCheckerTestResultDecider(urd, false);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String toolchain : TOOLCHAINS) {
			for (final String setting : SETTINGS) {
				addTestCase(toolchain, "ltlAutomizer/" + setting, INPUT);
			}
		}
		return super.createTestCases();
	}

	private static DirectoryFileEndingsPair getPair(final String directory, final int limit) {
		return new DirectoryFileEndingsPair(directory, FILEENDINGS, limit);
	}

	private static DirectoryFileEndingsPair getPair(final String directory) {
		return new DirectoryFileEndingsPair(directory, FILEENDINGS);
	}
}
