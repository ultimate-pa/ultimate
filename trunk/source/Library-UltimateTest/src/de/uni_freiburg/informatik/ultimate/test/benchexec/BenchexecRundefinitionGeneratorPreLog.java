/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE UnitTest Library.
 *
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.benchexec;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.namespace.QName;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.benchexec.benchmark.Benchmark;
import de.uni_freiburg.informatik.ultimate.test.benchexec.benchmark.Option;
import de.uni_freiburg.informatik.ultimate.test.benchexec.benchmark.Rundefinition;
import de.uni_freiburg.informatik.ultimate.test.benchexec.benchmark.Tasks;
import de.uni_freiburg.informatik.ultimate.test.reporting.BaseTestLogfile;
import de.uni_freiburg.informatik.ultimate.test.reporting.IPreTestLog;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * The {@link BenchexecRundefinitionGeneratorPreLog} generates a benchexec rundefinition from a test suite s.t. the
 * testsuite can be run with benchexec.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class BenchexecRundefinitionGeneratorPreLog extends BaseTestLogfile implements IPreTestLog {

	private static final String MAX_MEMORY = CoreUtil.humanReadableByteCount(Runtime.getRuntime().maxMemory(), true);
	private final static QName QNAME_INCLUDE = new QName("", "include");
	private Benchmark mBenchexecBenchmark;

	public BenchexecRundefinitionGeneratorPreLog(final Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
	}

	/**
	 * Define a function that determines the main input and the additional inputs and their naming convention. You can
	 * use these variables for benchexec.
	 * <ul>
	 * <li>${benchmark_name} Name of benchmark execution
	 * <li>${benchmark_date} Timestamp of benchmark execution
	 * <li>${benchmark_path} Directory of benchmark XML file
	 * <li>${benchmark_path_abs} Directory of benchmark XML file (absolute path)
	 * <li>${benchmark_file} Name of benchmark XML file (without path)
	 * <li>${logfile_path} Directory where tool-output files will be stored
	 * <li>${logfile_path_abs} Directory where tool-output files will be stored (absolute path)
	 * <li>${rundefinition_name} Name of current run definition
	 * <li>${inputfile_name} Name of current input file (without path)
	 * <li>${inputfile_path} Directory of current input file
	 * <li>${inputfile_path_abs} Directory of current input file (absolute path)
	 * </ul>
	 *
	 *
	 * @param ultimateTestSuite
	 * @param bla
	 */
	public BenchexecRundefinitionGeneratorPreLog(final Class<? extends UltimateTestSuite> ultimateTestSuite,
			final Function<String[], String> funGetMainInput, final String[] additionalInputs) {
		super(ultimateTestSuite);
	}

	@Override
	public String getFilenameExtension() {
		return ".xml";
	}

	@Override
	public String getLog() {
		try {
			return BenchmarkSerializer.toString(mBenchexecBenchmark);
		} catch (final JAXBException e) {
			throw new RuntimeException(e);
		}
	}

	@Override
	public void addAllTests(final List<UltimateRunDefinition> runs) {

		final Set<Long> timeouts = runs.stream().map(a -> a.getTimeout()).collect(Collectors.toSet());
		if (timeouts.size() != 1) {
			throw new IllegalArgumentException(
					"Cannot handle more than one timeout in a toolchain, and have seen " + timeouts);
		}
		if (runs.stream().anyMatch(a -> a.getInput().length != 1)) {
			throw new IllegalArgumentException("Cannot handle multiple input files in a run definition");
		}

		final long timeout = timeouts.iterator().next();
		final long timeoutInS = timeout / 1000;
		final long hardTimeoutInS = (long) (timeoutInS * 1.25);
		mBenchexecBenchmark = new Benchmark();
		mBenchexecBenchmark.setTimelimit(String.valueOf(timeoutInS));
		mBenchexecBenchmark.setHardtimelimit(String.valueOf(hardTimeoutInS));
		mBenchexecBenchmark.setCpuCores("2");
		mBenchexecBenchmark.setMemlimit(MAX_MEMORY);
		mBenchexecBenchmark.setTool("ultimateautomizer");

		// add rundefinitions to benchmaks
		final Set<Pair<File, File>> tcSettings =
				runs.stream().map(a1 -> new Pair<>(a1.getToolchain(), a1.getSettings())).collect(Collectors.toSet());

		final Map<Rundefinition, Set<File>> rundefsToTasks = new HashMap<>();
		for (final Pair<File, File> tcSetting : tcSettings) {
			final File toolchain = tcSetting.getFirst();
			final File setting = tcSetting.getSecond();

			final Rundefinition rd = new Rundefinition();
			rd.setName(toolchain.getName() + "+" + setting.getName());
			final List<Option> options = getOptions(toolchain, setting);
			rd.getTasksOrOptionOrPropertyfile().addAll(options);

			rundefsToTasks.put(rd,
					runs.stream().filter(a4 -> a4.getToolchain().equals(toolchain) && a4.getSettings().equals(setting))
							.map(a3 -> a3.getInput()[0]).collect(Collectors.toSet()));

			mBenchexecBenchmark.getRundefinitionOrOptionOrPropertyfile().add(rd);
		}

		final Set<File> inputs = runs.stream().map(a2 -> a2.getInput()[0]).collect(Collectors.toSet());
		if (rundefsToTasks.entrySet().stream().map(a -> a.getValue()).allMatch(a -> a.equals(inputs))) {
			// just add one task for all rundefinitions
			final Tasks tasks = new Tasks();
			tasks.setName("All");
			addFilesToTask(inputs, tasks);
			mBenchexecBenchmark.getRundefinitionOrOptionOrPropertyfile().add(tasks);
		} else {
			// add separate tasks for every rundefinition
			for (final Entry<Rundefinition, Set<File>> entry : rundefsToTasks.entrySet()) {
				final Tasks tasks = new Tasks();
				tasks.setName("RundefSpecific");
				addFilesToTask(entry.getValue(), tasks);
				entry.getKey().getTasksOrOptionOrPropertyfile().add(tasks);
			}
		}

	}

	private static void addFilesToTask(final Set<File> inputs, final Tasks tasks) {
		inputs.stream().map(a -> new JAXBElement<>(QNAME_INCLUDE, String.class, getPath(a)))
				.forEachOrdered(a -> tasks.getIncludeOrIncludesfileOrExclude().add(a));
	}

	private static List<Option> getOptions(final File toolchain, final File setting) {
		final List<Option> options = new ArrayList<>(2);
		final Option tc = new Option();
		tc.setName("-tc");
		tc.setContent(getPath(toolchain));
		options.add(tc);

		final Option s = new Option();
		s.setName("-s");
		s.setContent(getPath(setting));
		options.add(s);

		return options;
	}

	private static String getPath(final File file) {
		return file.getAbsolutePath().replaceAll("\\\\", "/");
	}
}
