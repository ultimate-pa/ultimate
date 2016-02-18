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
package de.uni_freiburg.informatik.ultimatetest.suites.svcomp;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiAutomizerTimingBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeCheckBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.logs.IncrementalLogWithBenchmarkResults;
import de.uni_freiburg.informatik.ultimatetest.logs.IncrementalLogWithVMParameters;
import de.uni_freiburg.informatik.ultimatetest.reporting.IIncrementalLog;
import de.uni_freiburg.informatik.ultimatetest.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimatetest.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimatetest.summaries.CsvSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.HTMLSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.KingOfTheHillSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.LatexDetailedSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.LatexOverviewSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.SVCOMPTestSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.TraceAbstractionTestSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimatetest.util.TestUtil;

/**
 * Test suite for SVCOMP15.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public abstract class AbstractSVCOMPTestSuite extends UltimateTestSuite {

	private IncrementalLogWithVMParameters mIncrementalLog;

	private ArrayList<UltimateTestCase> mTestCases;

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (mTestCases == null) {
			List<TestDefinition> testDefs = getTestDefinitions();
			File svcompRootDir = getSVCOMP15RootDirectory();

			Collection<File> setFiles = getAllSetFiles(svcompRootDir);
			Collection<File> allInputFiles = getAllPotentialInputFiles(svcompRootDir);

			if (testDefs == null || testDefs.isEmpty()) {
				System.err.println("No test definitions given. Did you implement getTestDefinitions correctly?");
				return new ArrayList<>();
			}

			if (allInputFiles == null || allInputFiles.isEmpty() || setFiles == null || setFiles.isEmpty()) {
				System.err
						.println("inputFiles or setFiles are null: did you specify the svcomp root directory correctly?"
								+ " Currently it is: " + svcompRootDir);
				return new ArrayList<>();
			}

			mTestCases = new ArrayList<>();

			for (TestDefinition def : testDefs) {
				List<UltimateTestCase> current = new ArrayList<>();
				String setFilename = def.getSetName() + ".set";
				for (File set : setFiles) {
					if (setFilename.equals(set.getName())) {
						addTestCases(def, set, allInputFiles, current, svcompRootDir);
					}
				}
				mTestCases.addAll(current);
			}

			mIncrementalLog.setCountTotal(mTestCases.size());
		}
		return mTestCases;
	}

	private void addTestCases(TestDefinition def, File setFile, Collection<File> possibleInputFiles,
			List<UltimateTestCase> testcases, File svcompRootDir) {

		Collection<File> inputFiles = getFilesForSetFile(possibleInputFiles, setFile);
		// use this for testing
		// inputFiles = Util.firstN(inputFiles, 3);
		for (File input : inputFiles) {

			try {
				// note: do not change the name without also checking
				// SVCOMP15TestSummary
				String name = createTestCaseName(svcompRootDir, input, def);
				UltimateRunDefinition urd = new UltimateRunDefinition(input, def.getSettings(), def.getToolchain());
				UltimateStarter starter = new UltimateStarter(urd, def.getTimeout());

				UltimateTestCase testCase = new UltimateTestCase(name, getTestResultDecider(urd), starter, urd,
						super.getSummaries(), super.getIncrementalLogs());

				testcases.add(testCase);
			} catch (Throwable ex) {
				System.err.println("Exception while creating test case, skipping this one: " + input.getAbsolutePath());
				ex.printStackTrace();
			}
		}

	}

	protected ITestResultDecider getTestResultDecider(UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, true);
	}

	private String createTestCaseName(File svcompRootDir, File input, TestDefinition def) {
		// note: do not change the name without also checking
		// SVCOMP15TestSummary
		StringBuilder sb = new StringBuilder();
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

	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		if (mIncrementalLog == null) {
			mIncrementalLog = new IncrementalLogWithVMParameters(getClass(), getTimeout());
		}
		return new IIncrementalLog[] { mIncrementalLog, new IncrementalLogWithBenchmarkResults(this.getClass()) };
	}

	@Override
	protected ITestSummary[] constructTestSummaries() {
		//@formatter:off
		ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks
			= new ArrayList<Class<? extends ICsvProviderProvider<? extends Object>>>();
		benchmarks.add(BuchiAutomizerTimingBenchmark.class);
		benchmarks.add(Benchmark.class);
		benchmarks.add(TraceAbstractionBenchmarks.class);
		benchmarks.add(CodeCheckBenchmarks.class);

		ColumnDefinition[] columnDef = new ColumnDefinition[]{
			new ColumnDefinition(
					"Runtime (ns)", "Avg. runtime",
					ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),	
			new ColumnDefinition(
					"Allocated memory end (bytes)", "Memory",
					ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
			new ColumnDefinition(
					"Overall iterations", "Iter{-}ations",
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"NumberOfCodeBlocks", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"SizeOfPredicatesFP", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
			new ColumnDefinition(
					"SizeOfPredicatesBP", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
			new ColumnDefinition(
					"Conjuncts in SSA", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),	
			new ColumnDefinition(
					"Conjuncts in UnsatCore", null,
					ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
			new ColumnDefinition(
					"ICC %", "ICC",
					ConversionContext.Percent(true,2), Aggregate.Ignore, Aggregate.Average),					
		};
	
		return new ITestSummary[] { 
				new SVCOMPTestSummary(getClass()), 
				new TraceAbstractionTestSummary(getClass()),
				new LatexOverviewSummary(getClass(), benchmarks, columnDef), 
				new LatexDetailedSummary(getClass(), benchmarks, columnDef),
				new CsvSummary(getClass(), benchmarks, columnDef),
				new HTMLSummary(getClass(), benchmarks, columnDef),
				new KingOfTheHillSummary(this.getClass()),
		};
		//@formatter:on
	}

	/**
	 * Override this if you want to use some special place for your SVCOMP15 repository. We default to
	 * trunk/examples/svcomp .
	 */
	protected File getSVCOMP15RootDirectory() {
		String svcompRootDir = TestUtil.getFromMavenVariableSVCOMPRoot(TestUtil.getPathFromTrunk("examples/svcomp"));
		return new File(svcompRootDir);
	}

	/**
	 * Supply your test definitions here
	 * 
	 * @return
	 */
	protected abstract List<TestDefinition> getTestDefinitions();

	/**
	 * -1 if you want all files per category, a value larger than 0 if you want to limit the number of files per
	 * TestDefinition.
	 * 
	 * @return
	 */
	protected abstract int getFilesPerCategory();

	protected abstract long getTimeout();

	private Collection<File> getFilesForSetFile(Collection<File> allFiles, File setFile) {

		List<String> regexes = new ArrayList<>();
		try {
			DataInputStream in = new DataInputStream(new FileInputStream(setFile));
			BufferedReader br = new BufferedReader(new InputStreamReader(in));
			String line;
			while ((line = br.readLine()) != null) {
				if (line.isEmpty()) {
					continue;
				}

				// the regexprs in the SVCOMP .set files are not platform
				// independent, so we change them slightly here
				line = line.replace("/", Pattern.quote(String.valueOf(File.separatorChar)));
				line = line.replace(".", "\\.").replace("*", ".*");
				line = ".*" + line;

				regexes.add(line);

			}
			in.close();
		} catch (Exception e) {
			e.printStackTrace();
		}
		ArrayList<File> currentFiles = new ArrayList<File>();
		int filesPerCategory = getFilesPerCategory();
		if (filesPerCategory == -1) {
			for (String regex : regexes) {
				currentFiles.addAll(TestUtil.filterFiles(allFiles, regex));
			}
		} else if (filesPerCategory > 0) {
			int filesPerSetLine = filesPerCategory / regexes.size();
			filesPerSetLine = filesPerSetLine <= 0 ? 1 : filesPerSetLine;
			for (String regex : regexes) {
				currentFiles.addAll(de.uni_freiburg.informatik.ultimate.core.util.CoreUtil
						.firstN(TestUtil.filterFiles(allFiles, regex), filesPerSetLine));
			}
		}

		return currentFiles;
	}

	private Collection<File> getAllSetFiles(File rootdir) {
		return getFilesRecursively(rootdir, new String[] { ".*\\.set" });
	}

	private Collection<File> getAllPotentialInputFiles(File rootdir) {
		return getFilesRecursively(rootdir, new String[] { ".*\\.c", ".*\\.i" });
	}

	private Collection<File> getFilesRecursively(File rootdir, String[] regex) {
		ArrayList<File> singleFiles = new ArrayList<File>();
		singleFiles.addAll(TestUtil.getFilesRegex(rootdir, regex));
		return singleFiles;
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
	protected TestDefinition getTestDefinitionFromExamples(String setname, String toolchain, String settings,
			long timeout) {
		return new TestDefinition(setname, new File(TestUtil.getPathFromTrunk("examples/toolchains/" + toolchain)),
				new File(TestUtil.getPathFromTrunk("examples/settings/" + settings)), timeout);
	}

	public class TestDefinition {
		private final String mSetname;
		private final File mToolchain;
		private final File mSettings;
		private final long mTimeout;

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
		 * 
		 * @author dietsch@informatik.uni-freiburg.de
		 */
		public TestDefinition(String setname, File toolchain, File settings, long timeout) {
			mSetname = setname;
			mToolchain = toolchain;
			mSettings = settings;
			mTimeout = timeout;
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
	}
}
