/*
 * Copyright (C) 2018 schaetzc@tf.uni-freiburg.de
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.automatascript;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.AutomataScriptTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.AutomataScriptTestSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.CsvConcatenator;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * @author schaetzc@tf.uni-freiburg.de
 */
public class DifferencePetriNwaBenchmark extends UltimateTestSuite {

	// @formatter:off
	private static final int TIMEOUT_MS = 30 * 60 * 1_000;
	private static final File TOOLCHAIN_FILE =
			new File(TestUtil.getPathFromTrunk("examples/toolchains/AutomataScriptInterpreter.xml"));
	private static final String[] DIRECTORIES = {
		"examples/Automata/benchmarks/pn/difference-small",
		"examples/Automata/benchmarks/pn/difference-small-reach-only"
	};
	private static final String[] FILE_ENDINGS = { ".ats" };
	private static final String[] SETTINGS = {
//		"AutomataScript/differencePetriNwa/differenceHeuristic.epf",
//		"AutomataScript/differencePetriNwa/differenceInverted.epf",
//		"AutomataScript/differencePetriNwa/differencePairwise.epf",
//		"AutomataScript/differencePetriNwa/differencePairwiseOnDemand.epf",
		"AutomataScript/differencePetriNwa/finPreDifferenceHeuristic.epf",
		"AutomataScript/differencePetriNwa/finPreDifferenceInverted.epf",
		"AutomataScript/differencePetriNwa/finPreDifferencePairwise.epf",
	};
	// @formatter:on
	
	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] { new AutomataScriptTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), AutomataOperationStatistics.class), };
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[] {};
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		final List<UltimateTestCase> testCases = new ArrayList<>();

		final Collection<File> inputFiles = new ArrayList<>();
		for (final String directory : DIRECTORIES) {
			inputFiles.addAll(getInputFiles(directory, FILE_ENDINGS));
		}

		for (final File inputFile : inputFiles) {
			for (final String settingFileName : SETTINGS) {
				final File settingsFile = new File(TestUtil.getPathFromTrunk(
						"/examples/settings/" + settingFileName));
				final UltimateRunDefinition urd = new UltimateRunDefinition(
						inputFile, settingsFile, TOOLCHAIN_FILE, TIMEOUT_MS);
				testCases.add(buildTestCase(urd, new AutomataScriptTestResultDecider()));
			}
		}
		Collections.sort(testCases);
		return testCases;
	}

	private static Collection<File> getInputFiles(final String directory, final String[] fileEndings) {
		return TestUtil.getFiles(new File(TestUtil.getPathFromTrunk(directory)), fileEndings);
	}

}
