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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.svcomp;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerModuleDecompositionBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerTimingBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeCheckBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimate.test.logs.incremental.IncrementalLogWithVMParameters;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.CsvConcatenator;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.CsvSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.HTMLSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.KingOfTheHillSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.LatexDetailedSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.LatexOverviewSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.SVCOMPTestSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.StandingsSummary;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimate.test.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.statistics.GraphSizeCsvProvider;

/**
 * Test suite for SVCOMP15.
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public abstract class AbstractSvcompTestSuite extends UltimateTestSuite {

	private IncrementalLogWithVMParameters mIncrementalLog;

	private ArrayList<UltimateTestCase> mTestCases;

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (mTestCases != null) {
			return mTestCases;
		}
		final List<SvcompTestDefinition> testDefs = getTestDefinitions();

		if (testDefs == null || testDefs.isEmpty()) {
			getLogger().error("No test definitions given. Did you implement getTestDefinitions correctly?");
			return new ArrayList<>();
		}

		final File svcompRootDir = getSVCOMPRootDirectory();
		final Collection<File> setFiles = getAllSetFiles(svcompRootDir);
		final Collection<File> allInputFiles = getAllPotentialInputFiles(svcompRootDir);
		if (allInputFiles == null || allInputFiles.isEmpty() || setFiles == null || setFiles.isEmpty()) {
			getLogger().error("inputFiles or setFiles are null: did you specify the svcomp root directory correctly?"
					+ " Currently it is: " + svcompRootDir);
			return new ArrayList<>();
		}

		final Map<String, File> setName2File = getName2File(setFiles);
		final Map<String, Collection<File>> set2InputFiles = getSetName2InputFiles(setName2File, allInputFiles);
		mTestCases = new ArrayList<>();

		for (final SvcompTestDefinition def : testDefs) {
			final List<UltimateTestCase> current = new ArrayList<>();
			final String setFileName = def.getSetName() + ".set";
			final Collection<File> inputFiles = set2InputFiles.get(setFileName);
			addTestCases(def, inputFiles, current, svcompRootDir);
			if (current.isEmpty()) {
				getLogger().error("No input file for set " + setFileName);
			}
			mTestCases.addAll(current);
		}

		mTestCases.sort(null);
		mIncrementalLog.setCountTotal(mTestCases.size());
		return mTestCases;
	}

	private void addTestCases(final SvcompTestDefinition def, final Collection<File> allInputFiles,
			final List<UltimateTestCase> testcases, final File svcompRootDir) {

		final int limit = def.getLimit() < 0 ? getFilesPerCategory() : def.getLimit();
		final Collection<File> inputFiles = TestUtil.limitFiles(allInputFiles, 0, limit);

		int i = 0;
		for (final File input : inputFiles) {
			try {
				// note: do not change the name without also checking
				// SVCOMP15TestSummary
				final String name = createTestCaseName(svcompRootDir, input, def);
				final UltimateRunDefinition urd =
						new UltimateRunDefinition(input, def.getSettings(), def.getToolchain(), def.getTimeout());
				testcases.add(buildTestCase(urd, getTestResultDecider(urd), name));
				++i;
			} catch (final Throwable ex) {
				getLogger().fatal("Exception while creating test case, skipping this one: " + input.getAbsolutePath(),
						ex);
			}
		}
		getLogger().info("Added " + i + " tests for " + def);
	}

	private Map<String, Collection<File>> getSetName2InputFiles(final Map<String, File> setName2File,
			final Collection<File> allInputFiles) {
		final Map<String, Collection<File>> rtr = new HashMap<>();
		for (final Entry<String, File> entry : setName2File.entrySet()) {
			rtr.put(entry.getKey(), getFilesForSetFile(allInputFiles, entry.getValue()));
		}
		return rtr;
	}

	private static Map<String, File> getName2File(final Collection<File> files) {
		final Map<String, File> rtr = new HashMap<>();
		for (final File file : files) {
			final File old = rtr.put(file.getName(), file);
			if (old != null) {
				throw new UnsupportedOperationException("Multiple files with the same name");
			}
		}
		return rtr;
	}

	private static String createTestCaseName(final File svcompRootDir, final File input,
			final SvcompTestDefinition def) {
		// note: do not change the name without also checking
		// SVCOMP15TestSummary
		final StringBuilder sb = new StringBuilder();
		sb.append(def.getSetName());
		sb.append(" ");
		sb.append(def.getToolchain().getName());
		sb.append(" ");
		sb.append(def.getSettings().getName());
		sb.append(": ");
		sb.append(input.getAbsolutePath().substring(svcompRootDir.getAbsolutePath().length(),
				input.getAbsolutePath().length()));
		return sb.toString();
	}

	protected ITestResultDecider getTestResultDecider(final UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, true);
	}

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		if (mIncrementalLog == null) {
			mIncrementalLog = new IncrementalLogWithVMParameters(getClass(), getTimeout());
		}
		return new IIncrementalLog[] { mIncrementalLog, new IncrementalLogWithBenchmarkResults(this.getClass()) };
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		final ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks = new ArrayList<>();
		benchmarks.add(BuchiAutomizerTimingBenchmark.class);
		benchmarks.add(Benchmark.class);
		benchmarks.add(TraceAbstractionBenchmarks.class);
		benchmarks.add(CodeCheckBenchmarks.class);
		benchmarks.add(BuchiAutomizerModuleDecompositionBenchmark.class);
		benchmarks.add(GraphSizeCsvProvider.class);
		benchmarks.add(FastUPRBenchmark.class);

		final ColumnDefinition[] columnDef = new ColumnDefinition[] {
				new ColumnDefinition("Runtime (ns)", "Avg. runtime", ConversionContext.Divide(1000000000, 2, " s"),
						Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition("Allocated memory end (bytes)", "Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.OverallIterations.toString(), "Iter{-}ations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.AbstIntIterations.toString(), "AI Iter{-}ations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.AbstIntStrong.toString(), "AI Strong",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.AbstIntTime.toString(), "AI Avg. Time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.OverallTime.toString(), "Trace Abstraction Time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_NumberOfCodeBlocks", null, ConversionContext.BestFitNumber(),
						Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_SizeOfPredicatesFP", null, ConversionContext.BestFitNumber(),
						Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_SizeOfPredicatesBP", null, ConversionContext.BestFitNumber(),
						Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_Conjuncts in SSA", null, ConversionContext.BestFitNumber(),
						Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("traceCheckStatistics_Conjuncts in UnsatCore", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("InterpolantCoveringCapability", "ICC", ConversionContext.Percent(true, 2),
						Aggregate.Ignore, Aggregate.Average), };

		final List<ITestSummary> rtr = new ArrayList<>();
		rtr.add(new SVCOMPTestSummary(getClass()));
		rtr.add(new LatexOverviewSummary(getClass(), benchmarks, columnDef));
		rtr.add(new LatexDetailedSummary(getClass(), benchmarks, columnDef));
		rtr.add(new TraceAbstractionTestSummary(getClass()));
		rtr.add(new CsvSummary(getClass(), benchmarks, columnDef));
		rtr.add(new HTMLSummary(getClass(), benchmarks, columnDef));
		rtr.add(new KingOfTheHillSummary(this.getClass()));
		rtr.add(new StandingsSummary(getClass()));
		benchmarks.stream().forEach(a -> rtr.add(new CsvConcatenator(getClass(), a)));

		return rtr.toArray(new ITestSummary[rtr.size()]);
	}

	/**
	 * Override this if you want to use some special place for your SVCOMP repository. We default to
	 * trunk/examples/svcomp .
	 */
	protected File getSVCOMPRootDirectory() {
		final String svcompRootDir =
				TestUtil.getFromMavenVariableSVCOMPRoot(TestUtil.getPathFromTrunk("examples/svcomp"));
		return new File(svcompRootDir);
	}

	/**
	 * Supply your test definitions here.
	 *
	 * @return A list of test definitions.
	 */
	protected abstract List<SvcompTestDefinition> getTestDefinitions();

	/**
	 * -1 if you want all files per category, a value larger than 0 if you want to limit the number of files per
	 * TestDefinition.
	 *
	 * @return
	 */
	protected abstract int getFilesPerCategory();

	protected abstract long getTimeout();

	private Collection<File> getFilesForSetFile(final Collection<File> allFiles, final File setFile) {
		final List<String> regexes = new ArrayList<>();
		try (final BufferedReader br =
				new BufferedReader(new InputStreamReader(new DataInputStream(new FileInputStream(setFile))))) {
			String line;
			while ((line = br.readLine()) != null) {
				if (line.isEmpty()) {
					continue;
				}

				// the regexprs in the SVCOMP .set files are not platform
				// independent, so we change them slightly here
				line = line.replace("/", Pattern.quote(String.valueOf(File.separatorChar)));
				line = line.replace(".", "\\.").replace("*", ".*");
				regexes.add(".*" + line);
			}
		} catch (final Exception e) {
			getLogger().fatal(e);
		}

		final List<File> currentFiles = new ArrayList<>();
		for (final String regex : regexes) {
			currentFiles.addAll(TestUtil.filterFiles(allFiles, regex));
		}
		if (currentFiles.isEmpty()) {
			getLogger().fatal("Could not find files matching the set file " + setFile);
		}
		return currentFiles;
	}

	private static Collection<File> getAllSetFiles(final File rootdir) {
		return TestUtil.getFilesRegex(rootdir, new String[] { ".*\\.set" });
	}

	private static Collection<File> getAllPotentialInputFiles(final File rootdir) {
		return TestUtil.getFilesRegex(rootdir, new String[] { ".*\\.c", ".*\\.i" });
	}

	/**
	 * @param setname
	 *            Case-sensitive name of the .set file without the suffix and without the path, e.g.
	 *            ControlFlowInteger.false-unreach-label or Simple
	 * @param toolchain
	 *            Path to .xml file describing the toolchain relative to trunk/examples/toolchains, e.g.
	 *            "AutomizerBpl.xml"
	 * @param settings
	 *            Path to .xml file describing the toolchain relative to trunk/examples/settings, e.g.
	 *            "automizer/BackwardPredicates.epf"
	 * @param timeout
	 *            Timeout in ms after which Ultimate should timeout. Overrides timeout in settings. Values <= 0 disable
	 *            the timeout (Timeout in settings still applies).
	 */
	protected SvcompTestDefinition getTestDefinitionFromExamples(final String setname, final String toolchain,
			final String settings, final long timeout) {
		return getTestDefinitionFromExamples(setname, toolchain, settings, timeout, -1);
	}

	/**
	 * @param setname
	 *            Case-sensitive name of the .set file without the suffix and without the path, e.g.
	 *            ControlFlowInteger.false-unreach-label or Simple
	 * @param toolchain
	 *            Path to .xml file describing the toolchain relative to trunk/examples/toolchains, e.g.
	 *            "AutomizerBpl.xml"
	 * @param settings
	 *            Path to .xml file describing the toolchain relative to trunk/examples/settings, e.g.
	 *            "automizer/BackwardPredicates.epf"
	 * @param timeout
	 *            Timeout in ms after which Ultimate should timeout. Overrides timeout in settings. Values <= 0 disable
	 *            the timeout (Timeout in settings still applies).
	 * @param limit
	 *            How many files from this set should be used.
	 */
	protected SvcompTestDefinition getTestDefinitionFromExamples(final String setname, final String toolchain,
			final String settings, final long timeout, final int limit) {
		return new SvcompTestDefinition(setname,
				new File(TestUtil.getPathFromTrunk("examples/toolchains/" + toolchain)),
				new File(TestUtil.getPathFromTrunk("examples/settings/" + settings)), timeout, limit);
	}

	protected SvcompTestDefinition getTestDefinitionFromExamplesOrNull(final String setname, final String toolchain,
			final String settings, final long timeout, final int limit) {
		try {
			return getTestDefinitionFromExamples(setname, toolchain, settings, timeout, limit);
		} catch (final Exception ex) {
			getLogger().error("Skipping " + setname + ", " + toolchain + ", " + settings + ", " + timeout + ", " + limit
					+ "because of ", ex);
			return null;
		}
	}

	protected final static class SvcompTestDefinition {
		private final String mSetname;
		private final File mToolchain;
		private final File mSettings;
		private final long mTimeout;
		private final int mLimit;

		/**
		 *
		 * @param setname
		 *            Case-sensitive name of the .set file without the suffix and without the path, e.g.
		 *            ControlFlowInteger.false-unreach-label or Simple
		 * @param toolchain
		 *            Path to .xml file describing the toolchain.
		 * @param settings
		 *            Path to .epf file describing the settings.
		 * @param timeout
		 *            Timeout in ms after which Ultimate should timeout. Overrides timeout in settings. Values <= 0
		 *            disable the timeout (Timeout in settings still applies).
		 * @param limit
		 *            How many files from this set should be used.
		 *
		 * @author dietsch@informatik.uni-freiburg.de
		 */
		private SvcompTestDefinition(final String setname, final File toolchain, final File settings,
				final long timeout, final int limit) {
			mSetname = setname;
			mToolchain = toolchain;
			mSettings = settings;
			mTimeout = timeout;
			mLimit = limit;
		}

		public String getSetName() {
			return mSetname;
		}

		public File getToolchain() {
			return mToolchain;
		}

		public File getSettings() {
			return mSettings;
		}

		public long getTimeout() {
			return mTimeout;
		}

		public int getLimit() {
			return mLimit;
		}

		@Override
		public String toString() {
			if (getLimit() == -1) {
				return getSetName();
			}
			return getSetName() + "(limit=" + getLimit() + ")";

		}
	}
}
