/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimatetest.suites.tacasminimization;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateStarter;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.AutomataScriptTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.reporting.CsvConcatenator;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderColumnFilter;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderRowFilter;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderTransformer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimatetest.summaries.AutomataScriptTestSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimatetest.summaries.LatexOverviewSummary;

/**
 * Test class to produce benchmark results.
 * <p>
 * Compares the internal to an external partial Max-SAT solver.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class CompareToDimacsTestSuite extends UltimateTestSuite {
	private static final String mToolchain = "examples/toolchains/AutomataScriptInterpreter.xml";
	private static final File mToolchainFile = new File(TestUtil.getPathFromTrunk(mToolchain));
	private static int mTimeout = 30 * 1000;

	private static final String[] mDirectories = { "examples/Automata/random", };
	private static final String[] mFileEndings = { ".ats" };

	private static final String[] SETTINGS = { "AutomataScript/shrinkNwa.epf", "AutomataScript/minimizeNwaMaxSat2.epf",
			"AutomataScript/minimizeNwaPmaxSatDimacs.epf" };

	private static final String[] INTERESTING_COLUMNS = { "File",
			// "Settings",
			// StatisticsType.ATS_ID.toString(),
			StatisticsType.OPERATION_NAME.toString(), StatisticsType.RUNTIME_TOTAL.toString(),
			StatisticsType.STATES_INPUT.toString(), StatisticsType.STATES_OUTPUT.toString(),
			StatisticsType.STATES_REDUCTION_ABSOLUTE.toString(), StatisticsType.STATES_REDUCTION_RELATIVE.toString(),
			StatisticsType.SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS.toString(), };
	private static final Set<String> INTERESTING_COLUMNS_AS_SET = new HashSet<>(Arrays.asList(INTERESTING_COLUMNS));

	private static final Object[] INTERESTING_OPERATIONS =
			{ "minimizeNwaMaxSat2", "shrinkNwa", "minimizeNwaPmaxSatDimacs", };
	private static final Set<Object> INTERESTING_OPERATIONS_AS_SET =
			new HashSet<>(Arrays.asList(INTERESTING_OPERATIONS));

	@Override
	protected ITestSummary[] constructTestSummaries() {
		final ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = new ArrayList<>();

		final ColumnDefinition[] columnDef = new ColumnDefinition[] {
				new ColumnDefinition(CegarLoopStatisticsDefinitions.OverallTime.toString(), "Avg. runtime",
						ConversionContext.Divide(1_000_000_000, 2, " s"), Aggregate.Sum, Aggregate.Average), };

		final Predicate<String> columnPredicate = (x -> INTERESTING_COLUMNS_AS_SET.contains(x));
		final Map<String, Set<Object>> column2allowedValues =
				Collections.singletonMap(StatisticsType.OPERATION_NAME.toString(), INTERESTING_OPERATIONS_AS_SET);
		final Predicate<Pair<List<Object>, List<String>>> predicate =
				new CsvProviderRowFilter.AllowedValuesRowFilter<>(column2allowedValues);

		final List<ICsvProviderTransformer<Object>> transformers = new ArrayList<>();
		transformers.add(new CsvProviderColumnFilter<>(columnPredicate));
		transformers.add(new CsvProviderRowFilter<>(predicate));

		return new ITestSummary[] { new AutomataScriptTestSummary(this.getClass()),
				new CsvConcatenator(this.getClass(), AutomataOperationStatistics.class),
				new CsvConcatenator(this.getClass(), AutomataOperationStatistics.class, transformers),
				new LatexOverviewSummary(getClass(), benchmarks, columnDef), };
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[0];
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		final List<UltimateTestCase> testCases = new ArrayList<>();

		final Collection<File> inputFiles = new ArrayList<>();
		for (final String directory : mDirectories) {
			inputFiles.addAll(getInputFiles(directory, mFileEndings));
		}

		for (final File inputFile : inputFiles) {
			for (final String settingFileName : SETTINGS) {
				final File settingsFile = new File(TestUtil.getPathFromTrunk("/examples/settings/" + settingFileName));
				final UltimateRunDefinition urd = new UltimateRunDefinition(inputFile, settingsFile, mToolchainFile);
				final UltimateStarter starter = new UltimateStarter(urd, mTimeout);
				final UltimateTestCase utc = new UltimateTestCase(urd.generateShortStringRepresentation(),
						new AutomataScriptTestResultDecider(), starter,
						// mDescription + "_" + inputFile.getAbsolutePath(),
						urd, super.getSummaries(), null);
				testCases.add(utc);
			}
		}
		testCases.sort(null);
		return testCases;
	}

	private static Collection<File> getInputFiles(final String directory, final String[] fileEndings) {
		return TestUtil.getFiles(new File(TestUtil.getPathFromTrunk(directory)), fileEndings);
	}
}
