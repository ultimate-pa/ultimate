/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.NoErrorTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.junitextension.testfactory.TestFactory;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class SmtUnusedSymbolFilter extends UltimateTestSuite {

	// @formatter:off
	public static final String TEST_FILES_DIR = 
			"../../tmp/smtBenchmarks/invariantSynthesis/InvariantSynthesisBenchmarks/reallyFNI/clean/difficult/";
	public static final String TOOLCHAIN = "examples/toolchains/LassoRanker.xml";
	public static final String SETTINGS_FILE = "examples/settings/FilterUnusedDeclarationsFromSmtFile.epf";

	public static final long DEADLINE = 500 * 1000; // in ms

	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] { };
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[] { };
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
			final UltimateRunDefinition urd = new UltimateRunDefinition(inputFile, settingsFile, toolchainFile);
			final ITestResultDecider decider = new NoErrorTestResultDecider(urd);
			rtr.add(buildTestCase(urd, DEADLINE, decider, inputFile.getName()));
		}

		return rtr;
	}

	public Collection<File> getInputFiles() {
		return TestUtil.getFiles(new File(TestUtil.getPathFromTrunk(TEST_FILES_DIR)), new String[] { ".smt2" });
	}
	
	// @formatter:on

}
