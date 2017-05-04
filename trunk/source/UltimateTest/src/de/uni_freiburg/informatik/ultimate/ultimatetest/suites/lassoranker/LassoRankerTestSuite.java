/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jan Leike (leike@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.lassoranker;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.LassoRankerTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.LassoRankerTestResultDecider.ExpectedResult;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.TestFactory;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.ultimatetest.logs.IncrementalLogWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimate.ultimatetest.summaries.CsvConcatenator;
import de.uni_freiburg.informatik.ultimate.ultimatetest.summaries.TraceAbstractionTestSummary;

/**
 * Test Suite for the LassoRanker plugin
 *
 * The Test Suite calls the LassoRanker on all '.bpl'-files found in the directory specified by s_test_files_dir and
 * uses the toolchain s_toolchain.
 *
 * The files in the test file directory as assumed to be annotated with an expected result value in their first line.
 * The annotation has the form
 *
 * <pre>
 * // #rExpectedResult
 * </pre>
 *
 * where ExpectedResult can be one of the following.
 *
 * <ul>
 * <li>"Ignore" -- do not use this as a test file
 * <li>"Termination" -- example terminates, but LassoRanker may not prove it
 * <li>"TerminationDerivable" -- LassoRanker should prove that this example terminates
 * <li>"NonTermination" -- example does not terminate, but LassoRanker may not prove it
 * <li>"NonTerminationDerivable" -- LassoRanker should prove that this example does not terminate
 * <li>"Unknown" -- termination is unspecified
 * <li>"Error" -- LassoRanker should throw an error when processing this example
 * </ul>
 *
 * @see LassoRankerTestResultDecider.ExpectedResult
 *
 * @author Jan Leike
 */
public class LassoRankerTestSuite extends UltimateTestSuite {
	public static final String TEST_FILES_DIR = "examples/lassos/";
	public static final String TOOLCHAIN = "examples/toolchains/LassoRanker.xml";
	// Workaround by Matthias: Use following line for linear constraints
	// public static final String s_settings_file =
	// "examples/settings/LassoRankerTestLinearSMTInterpol.epf";
	// Workaround by Matthias: Use following line for non-linear constraints
	public static final String SETTINGS_FILE = "examples/settings/LassoRankerTest.epf";

	public static final long DEADLINE = 5 * 1000; // in ms

	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] { new TraceAbstractionTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), TraceAbstractionBenchmarks.class) };
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[] { new IncrementalLogWithBenchmarkResults(this.getClass()) };
	}

	@Override
	@TestFactory
	public Collection<UltimateTestCase> createTestCases() {
		final List<UltimateTestCase> rtr = new ArrayList<>();
		final List<File> inputFiles = new ArrayList<>(getInputFiles());
		Collections.sort(inputFiles);

		final File toolchainFile = new File(TestUtil.getPathFromTrunk(TOOLCHAIN));
		final File settingsFile = new File(TestUtil.getPathFromTrunk(SETTINGS_FILE));
		for (final File inputFile : inputFiles) {
			final UltimateRunDefinition urd =
					new UltimateRunDefinition(inputFile, settingsFile, toolchainFile, DEADLINE);
			final LassoRankerTestResultDecider decider = new LassoRankerTestResultDecider(inputFile);
			if (decider.getExpectedResult() == ExpectedResult.IGNORE) {
				continue;
			}
			rtr.add(buildTestCase(urd, decider, inputFile.getName()));
		}

		return rtr;
	}

	public Collection<File> getInputFiles() {
		return TestUtil.getFiles(new File(TestUtil.getPathFromTrunk(TEST_FILES_DIR)), new String[] { ".bpl" });
	}

}
