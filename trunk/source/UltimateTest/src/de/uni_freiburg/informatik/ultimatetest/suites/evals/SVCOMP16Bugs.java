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

package de.uni_freiburg.informatik.ultimatetest.suites.evals;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.util.relation.Quad;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class SVCOMP16Bugs extends AbstractEvalTestSuite {
	private static final String[] ALL_C = new String[] { ".c", ".i" };
	private static final String[] BPL = new String[] { ".bpl" };
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;

	private static final String OVERFLOW = "svcomp2016/svcomp-Overflow-64bit-Automizer_Default.epf";
	private static final String BIT = "svcomp2016/svcomp-Reach-32bit-Automizer_Bitvector.epf";
	private static final String AUTOMIZER = "AutomizerC.xml";
	private static final String TERMAUTOMIZER = "BuchiAutomizerCWithBlockEncoding.xml";

	// @formatter:off
	@SuppressWarnings("unchecked")
	private static final Quad<String, String[], String,String[]>[] DEFS = new Quad[] {
			new Quad<>(AUTOMIZER, ALL_C, BIT, sv("bitvector-regression/integerpromotion_false-unreach-call.i")),
			new Quad<>(AUTOMIZER, ALL_C, OVERFLOW, sv("signedintegeroverflow-regression/AdditionIntMin_false-no-overflow.c.i")),
	};
	// @formatter:on

	private static String[] sv(final String path) {
		return new String[] { "examples/svcomp/" + path };
	}

	@Override
	protected long getTimeout() {
		return 60 * 1000;
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		// @formatter:off
		return new ColumnDefinition[] {
				new ColumnDefinition("Runtime (ns)", "Total time", ConversionContext.Divide(1000000000, 2, " s"),
						Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition("Allocated memory end (bytes)", "Alloc. Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
				new ColumnDefinition("Peak memory consumption (bytes)", "Peak Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average), };
		// @formatter:on
	}

	@Override
	public ITestResultDecider constructITestResultDecider(UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, false);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final Quad<String, String[], String, String[]> triple : DEFS) {
			final String[] input = triple.getFourth();
			final DirectoryFileEndingsPair[] pairs = new DirectoryFileEndingsPair[input.length];
			for (int i = 0; i < input.length; ++i) {
				pairs[i] = new DirectoryFileEndingsPair(input[i], triple.getSecond(), DEFAULT_LIMIT);
			}
			addTestCases(triple.getFirst(), triple.getThird(), pairs);
		}
		return super.createTestCases();
	}
}
