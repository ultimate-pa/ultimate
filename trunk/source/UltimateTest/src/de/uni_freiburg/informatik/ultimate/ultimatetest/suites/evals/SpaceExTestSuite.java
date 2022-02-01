/*
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public class SpaceExTestSuite extends AbstractEvalTestSuite {
	
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;
	
	//@formatter:off
	@SuppressWarnings("unchecked")
	private static final Triple<String, String, String>[] TOOLCHAINS = new Triple[] {
	       //new Triple<>("SpaceExParserWithTA.xml", ".xml", "spaceex/spaceex_parser_testing_ModelsAndUnsatCore_DEBUG.epf"),
	       // new Triple<>("SpaceExParserWithTA.xml", ".xml", "spaceex/spaceex_parser_testing_InternalSmtInterpol_DEBUG.epf"),
	       // new Triple<>("SpaceExParserWithTA.xml", ".xml", "spaceex/spaceex_parser_testing_ExternalZ3_DEBUG.epf"),
	        new Triple<>("SpaceExParserWithTA.xml", ".xml", "spaceex/spaceex_parser_testing_ExternalZ3.epf"),
	};
	//@formatter:on
	
	//@formatter:off
	private static final String[] INPUT = new String[] {
//		"examples/hybrid/spaceex/",
// 	    "examples/hybrid/spaceex/bigstuff",
//		"examples/hybrid/spaceex/tanks/test",
//		"examples/hybrid/spaceex/tanks/safe",
	    "examples/hybrid/spaceex/simple",
	    "examples/hybrid/spaceex/regression",
        "examples/hybrid/spaceex/misc",
		"examples/hybrid/spaceex/linear",
		"examples/hybrid/spaceex/tanks/unsafe",
	};
	//@formatter:on
	
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
	protected long getTimeout() {
		// 15 min
		return 900000;
	}
	
	@Override
	protected ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, false);
	}
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final Triple<String, String, String> triple : TOOLCHAINS) {
			final DirectoryFileEndingsPair[] pairs = new DirectoryFileEndingsPair[INPUT.length];
			for (int i = 0; i < INPUT.length; ++i) {
				pairs[i] = new DirectoryFileEndingsPair(INPUT[i], new String[] { triple.getSecond() }, DEFAULT_LIMIT);
			}
			addTestCase(triple.getFirst(), triple.getThird(), pairs);
		}
		return super.createTestCases();
	}
	
}
