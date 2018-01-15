/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.evals;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;
import java.util.TreeSet;

import org.junit.AfterClass;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase.AfterTest;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.test.util.UltimateRunDefinitionGenerator;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;

/**
 * Test suite that allows regression verification for different revisions of programs.
 *
 * This testsuite is tailored to the benchmarks provided in a
 * <a href="https://www.sosy-lab.org/research/cpa-reuse/regression-benchmarks/index.html">ESEC/FSE 2013 paper on
 * "Precision Reuse for Efficient Regression Verification"</a>.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class RegressionVerificationTestSuite extends AbstractEvalTestSuite {

	private final String BENCHMARK_DIR = "examples/regression-verif";

	private final File TOOLCHAIN = UltimateRunDefinitionGenerator.getFileFromToolchainDir("AutomizerC.xml");

	private final File SETTINGS_FIRST_REV = UltimateRunDefinitionGenerator
			.getFileFromSettingsDir("regression-verif/svcomp-Reach-64bit-Automizer_Default_NoReuse_DumpAts.epf");
	private final File SETTINGS_REST_REV = UltimateRunDefinitionGenerator
			.getFileFromSettingsDir("regression-verif/svcomp-Reach-64bit-Automizer_Default_EagerReuse.epf");
	private final File ATS_DUMP_DIR = new File("./automata-dump");
	private final boolean ONLY_FIRST = true;
	private final boolean ONLY_REST = false;

	@Override
	protected long getTimeout() {
		return 90 * 1000;
	}

	@Override
	public ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		return new SafetyCheckTestResultDecider(urd, true);
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {

		ATS_DUMP_DIR.mkdirs();

		final Collection<UltimateRunDefinition> urds = new ArrayList<>();
		// list all example programs with their first revision
		final String fullPath = TestUtil.getPathFromTrunk(BENCHMARK_DIR);
		final Map<String, TreeSet<File>> program2ListOfRevisions = getProgram2Revisions(fullPath);

		for (final Entry<String, TreeSet<File>> entry : program2ListOfRevisions.entrySet()) {
			final Iterator<File> revIter = entry.getValue().iterator();
			runAllWithFirstRevAts(revIter, urds);
		}

		// call addTestCase
		addTestCase(urds);
		return super.createTestCases();
	}

	/**
	 * Generate test cases where we generate an .ats file from the first revision and use it for all the following
	 * revisions.
	 */
	private void runAllAndGenerateFirstRevAts(final Iterator<File> revIter,
			final Collection<UltimateRunDefinition> urds) {
		// do first revision without input automaton
		final File atsFileForLaterRevisions;
		if (revIter.hasNext()) {
			final File firstRevFile = revIter.next();
			final String firstRevPrefix = firstRevFile.getName().substring(0, 3);
			final File atsFile = new File(ATS_DUMP_DIR, firstRevPrefix + "AutomataForReuse.ats");
			atsFileForLaterRevisions = getFirstRevAtsFile(firstRevFile);
			if (!ONLY_REST) {
				final AfterTest funAfterTest = () -> renameAndMove(firstRevFile, atsFile);
				urds.add(new UltimateRunDefinition(firstRevFile, SETTINGS_FIRST_REV, TOOLCHAIN, getTimeout(),
						funAfterTest));
			}
		} else {
			return;
		}

		if (ONLY_FIRST) {
			return;
		}

		while (revIter.hasNext()) {
			final File currentRev = revIter.next();
			urds.add(new UltimateRunDefinition(new File[] { currentRev, atsFileForLaterRevisions }, SETTINGS_REST_REV,
					TOOLCHAIN, getTimeout()));
		}
	}

	/**
	 * Generate test cases where we use the .ats file from the first revision for all the revisions.
	 */
	private void runAllWithFirstRevAts(final Iterator<File> revIter, final Collection<UltimateRunDefinition> urds) {
		final File atsFileForLaterRevisions;
		if (revIter.hasNext()) {
			final File firstRevFile = revIter.next();
			atsFileForLaterRevisions = getFirstRevAtsFile(firstRevFile);
			if (!ONLY_REST) {
				urds.add(new UltimateRunDefinition(new File[] { firstRevFile, atsFileForLaterRevisions },
						SETTINGS_REST_REV, TOOLCHAIN, getTimeout()));
			}
		} else {
			return;
		}

		if (ONLY_FIRST) {
			return;
		}

		while (revIter.hasNext()) {
			final File currentRev = revIter.next();
			urds.add(new UltimateRunDefinition(new File[] { currentRev, atsFileForLaterRevisions }, SETTINGS_REST_REV,
					TOOLCHAIN, getTimeout()));
		}
	}

	private static File getFirstRevAtsFile(final File inputFile) {
		final Path target = Paths.get(inputFile.getParent(), inputFile.getName() + "-firstRev.ats");
		return target.toFile();
	}

	private static void renameAndMove(final File inputFile, final File atsFile) {
		if (atsFile.exists()) {
			final Path target = getFirstRevAtsFile(inputFile).toPath();
			try {
				Files.move(atsFile.toPath(), target, StandardCopyOption.REPLACE_EXISTING);
			} catch (final IOException e) {
				e.printStackTrace();
			}
		}

	}

	/**
	 * Orders the available programs by their revision.
	 *
	 * @param fullPath
	 *            The absolute path to the directory containing the benchmarks from this paper.
	 * @return A map from program name to ordered set of files (ascending by revisions).
	 */
	private static Map<String, TreeSet<File>> getProgram2Revisions(final String fullPath) {
		final File rootDir = new File(fullPath);
		final Comparator<File> numericComparator = new Comparator<File>() {

			@Override
			public int compare(final File o1, final File o2) {
				final String revStr1 = o1.getName().substring(0, 3);
				final String revStr2 = o2.getName().substring(0, 3);
				return Integer.compare(Integer.parseInt(revStr1), Integer.parseInt(revStr2));
			}
		};
		final Map<String, TreeSet<File>> program2ListOfRevisions = new TreeMap<>();
		final Iterator<File> dirIter = Arrays.stream(rootDir.list((file, name) -> file.isDirectory()))
				.map(a -> new File(rootDir, a)).iterator();
		while (dirIter.hasNext()) {
			final File currentDir = dirIter.next();
			// the dir name is the name of the program
			// the files there are named <revnumber>.<hash>.<file/kernel>.cil_<expectedresult>.<fileext>

			for (final File file : currentDir.listFiles()) {
				final String[] filenameparts = file.getName().split("\\.");
				if (filenameparts.length < 3) {
					System.err.println("Unknown naming for " + file.getName());
					continue;
				}
				final String fileId = currentDir.getName() + "-" + filenameparts[2];
				TreeSet<File> list = program2ListOfRevisions.get(fileId);
				if (list == null) {
					list = new TreeSet<>(numericComparator);
					program2ListOfRevisions.put(fileId, list);
				}
				list.add(file);
			}
		}
		return program2ListOfRevisions;
	}

	@AfterClass
	public void removeDumpedAts() {
		TestUtil.deleteDirectory(ATS_DUMP_DIR);
	}

	// @Override
	// protected IPreTestLog[] constructPreTestLogs() {
	// return new IPreTestLog[] { new BenchexecRundefinitionGeneratorPreLog(getClass()) };
	// }
}
