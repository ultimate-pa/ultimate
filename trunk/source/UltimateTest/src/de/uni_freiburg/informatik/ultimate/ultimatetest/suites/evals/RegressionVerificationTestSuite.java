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
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
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
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

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

	private static final String BENCHMARK_DIR = "examples/regression-verif";
	// private static final String ALLOWED_PROGS = "examples/regression-verif/successful_programs";
	private static final String ALLOWED_PROGS = null;

	private static final File TOOLCHAIN = UltimateRunDefinitionGenerator.getFileFromToolchainDir("AutomizerC.xml");

	private static final File SETTINGS_NO_REUSE_DUMP = UltimateRunDefinitionGenerator
			.getFileFromSettingsDir("regression-verif/svcomp-Reach-64bit-Automizer_Default_NoReuse_DumpAts.epf");
	private static final File SETTINGS_EAGER_REUSE = UltimateRunDefinitionGenerator
			.getFileFromSettingsDir("regression-verif/svcomp-Reach-64bit-Automizer_Default_EagerReuse.epf");
	private static final File SETTINGS_EAGER_REUSE_ONLY_NEW_LETTERS =
			UltimateRunDefinitionGenerator.getFileFromSettingsDir(
					"regression-verif/svcomp-Reach-64bit-Automizer_Default_EagerReuse_OnlyNewLetters.epf");
	private static final File SETTINGS_EAGER_REUSE_ONLY_NEW_LETTERS_SOLVER =
			UltimateRunDefinitionGenerator.getFileFromSettingsDir(
					"regression-verif/svcomp-Reach-64bit-Automizer_Default_EagerReuse_OnlyNewLettersSolver.epf");
	private static final File SETTINGS_VANILLA = UltimateRunDefinitionGenerator
			.getFileFromSettingsDir("regression-verif/svcomp-Reach-64bit-Automizer_Default.epf");
	private static final File SETTINGS_LAZY_REUSE = UltimateRunDefinitionGenerator
			.getFileFromSettingsDir("regression-verif/svcomp-Reach-64bit-Automizer_Default_LazyReuse.epf");
	private static final File SETTINGS_EAGER_REUSE_DUMP = UltimateRunDefinitionGenerator
			.getFileFromSettingsDir("regression-verif/svcomp-Reach-64bit-Automizer_Default_EagerReuse_DumpAts.epf");
	private static final File SETTINGS_EAGER_REUSE_DUMP_ONLY_NEW_LETTERS =
			UltimateRunDefinitionGenerator.getFileFromSettingsDir(
					"regression-verif/svcomp-Reach-64bit-Automizer_Default_EagerReuse_OnlyNewLetters_DumpAts.epf");
	private static final File SETTINGS_EAGER_REUSE_DUMP_ONLY_NEW_LETTERS_SOLVER =
			UltimateRunDefinitionGenerator.getFileFromSettingsDir(
					"regression-verif/svcomp-Reach-64bit-Automizer_Default_EagerReuse_OnlyNewLettersSolver_DumpAts.epf");
	private static final File SETTINGS_LAZY_REUSE_DUMP = UltimateRunDefinitionGenerator
			.getFileFromSettingsDir("regression-verif/svcomp-Reach-64bit-Automizer_Default_LazyReuse_DumpAts.epf");

	private static final File ATS_DUMP_DIR = new File("./automata-dump");

	// start with 0 for both params
	private static final int FIRST_N_PROGRAMS = Integer.MAX_VALUE;
	private static final int FIRST_N_REVISIONS_PER_PROGRAM = Integer.MAX_VALUE;

	public RegressionVerificationTestSuite() {
		super();
		mSortTestcases = false;
	}

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
		final Set<String> allowedPrograms;
		if (ALLOWED_PROGS != null) {
			final String allowedProgramsPath = TestUtil.getPathFromTrunk(ALLOWED_PROGS);
			allowedPrograms = getAllowedPrograms(allowedProgramsPath);
		} else {
			allowedPrograms = Collections.emptySet();
		}
		final String fullPath = TestUtil.getPathFromTrunk(BENCHMARK_DIR);
		final Map<String, TreeSet<File>> program2ListOfRevisions = getProgram2Revisions(fullPath);

		int programCount = 0;
		for (final Entry<String, TreeSet<File>> entry : program2ListOfRevisions.entrySet()) {
			if (FIRST_N_PROGRAMS < programCount) {
				break;
			}

			final TreeSet<File> revisions = prune(entry.getValue());

			if (!isAllowed(allowedPrograms, revisions)) {
				System.err.println(entry.getKey() + " is not allowed");
				continue;
			}

			final String marker = "noReuse";
			final File targetAtsFile = getAtsFile(revisions.first(), marker);

			// dump .ats for the first/all (depending on last param) revision(s) of the program
			// runDumpNoReuse(revisions.iterator(), urds, SETTINGS_NO_REUSE_DUMP, marker, true);

			// run reuse with the .ats from the first revision of the program
			// runNoDumpReuseSpecificRevision(revisions.iterator(), urds, SETTINGS_EAGER_REUSE, targetAtsFile);
			// runNoDumpReuseSpecificRevision(revisions.iterator(), urds, SETTINGS_EAGER_REUSE_ONLY_NEW_LETTERS,
			// targetAtsFile);
			// runNoDumpReuseSpecificRevision(revisions.iterator(), urds, SETTINGS_EAGER_REUSE_ONLY_NEW_LETTERS_SOLVER,
			// targetAtsFile);
			// runNoDumpReuseSpecificRevision(revisions.iterator(), urds, SETTINGS_LAZY_REUSE, targetAtsFile);
			//

			// run reuse on the whole sequence (dump from rev i is input for rev i+1, rev 0 has no input)
			runDumpReusePreviousRevision(revisions, urds, SETTINGS_EAGER_REUSE_DUMP);
			runDumpReusePreviousRevision(revisions, urds, SETTINGS_LAZY_REUSE_DUMP);

			// runDumpReusePreviousRevision(revisions, urds, SETTINGS_EAGER_REUSE_DUMP_ONLY_NEW_LETTERS);
			// runDumpReusePreviousRevision(revisions, urds, SETTINGS_EAGER_REUSE_DUMP_ONLY_NEW_LETTERS_SOLVER);

			// run vanilla for comparison
			runNoDumpNoReuse(revisions.iterator(), urds, SETTINGS_VANILLA);
			programCount++;
		}

		// call addTestCase
		addTestCase(urds);
		return super.createTestCases();
	}

	/**
	 * If we want to analyse only the first revisions of all programs, remove all other revisions from the
	 * {@link TreeSet}.
	 */
	private TreeSet<File> prune(final TreeSet<File> value) {
		if (value.isEmpty()) {
			return value;
		}
		final TreeSet<File> rtr = new TreeSet<>();
		final Iterator<File> iter = value.iterator();
		for (int i = 0; i < FIRST_N_REVISIONS_PER_PROGRAM && iter.hasNext(); ++i) {
			rtr.add(iter.next());
		}

		return rtr;
	}

	/**
	 * Generate test cases where we generate .ats files for all revisions but do not use .ats files as input
	 */
	private void runDumpNoReuse(final Iterator<File> revIter, final Collection<UltimateRunDefinition> urds,
			final File settings, final String marker, final boolean onlyFirstRevision) {
		int internalRevision = 0;
		while (revIter.hasNext()) {
			final File currentProgram = revIter.next();
			if (onlyFirstRevision && internalRevision > 0) {
				break;
			}
			final File dumpedAtsFile = new File(ATS_DUMP_DIR, currentProgram.getName() + "-reuse.ats");

			final AfterTest funAfterTest = () -> renameAndMove(currentProgram, dumpedAtsFile, marker);
			urds.add(new UltimateRunDefinition(currentProgram, settings, TOOLCHAIN, getTimeout(), funAfterTest));

			internalRevision++;
		}
	}

	/**
	 * Generate test cases where we use the .ats file from some revision for all the revisions of a program. Expects
	 * that the .ats file exists when the test case is executed.
	 */
	private void runNoDumpReuseSpecificRevision(final Iterator<File> revIter,
			final Collection<UltimateRunDefinition> urds, final File settings, final File targetAtsFile) {

		while (revIter.hasNext()) {
			final File currentProgram = revIter.next();
			urds.add(new UltimateRunDefinition(new File[] { currentProgram, targetAtsFile }, settings, TOOLCHAIN,
					getTimeout()));
		}
	}

	/**
	 * Generate test cases where we use the .ats file from some revision for all the revisions of a program. Expects
	 * that the .ats file exists when the test case is executed.
	 */
	private void runDumpReusePreviousRevision(final TreeSet<File> revisions,
			final Collection<UltimateRunDefinition> urds, final File settings) {
		final String marker = "reuse";

		File previousRev = null;
		File currentRev = null;
		final Iterator<File> revIter = revisions.iterator();
		while (revIter.hasNext()) {
			previousRev = currentRev;
			currentRev = revIter.next();
			final File currentAtsFile = new File(ATS_DUMP_DIR, currentRev.getName() + "-reuse.ats");
			final File finalCurrentRev = currentRev;
			final AfterTest funAfterTest = () -> renameAndMove(finalCurrentRev, currentAtsFile, marker);
			if (previousRev == null) {
				urds.add(new UltimateRunDefinition(currentRev, settings, TOOLCHAIN, getTimeout(), funAfterTest));
			} else {
				final File previousAtsFile = getAtsFile(previousRev, marker);
				urds.add(new UltimateRunDefinition(new File[] { currentRev, previousAtsFile }, settings, TOOLCHAIN,
						getTimeout(), funAfterTest));
			}
		}
	}

	/**
	 * Generate test cases where we just use program revisions as input and neither dump nor use .ats files.
	 */
	private void runNoDumpNoReuse(final Iterator<File> revIter, final Collection<UltimateRunDefinition> urds,
			final File settings) {
		while (revIter.hasNext()) {
			final File currentProgram = revIter.next();
			urds.add(new UltimateRunDefinition(currentProgram, settings, TOOLCHAIN, getTimeout()));
		}
	}

	/**
	 * Get the name of the .ats file produced from the given input file with the given settings.
	 *
	 * @param inputFile
	 *            The input file for which the .ats file was dumped
	 * @param marker
	 *            A marker string that describes whether the file was created by running without reuse or with reuse.
	 * @return A file object that points to the .ats file (the file may not yet exist)
	 */
	private static File getAtsFile(final File inputFile, final String marker) {
		final Path target = Paths.get(inputFile.getParent(), inputFile.getName() + "-reuse.ats");
		return target.toFile();
	}

	private static void renameAndMove(final File currentProgram, final File atsFile, final String marker) {
		if (atsFile.exists()) {
			final Path target = getAtsFile(currentProgram, marker).toPath();
			try {
				Files.move(atsFile.toPath(), target, StandardCopyOption.REPLACE_EXISTING);
				CoreUtil.deleteDirectoryContents(ATS_DUMP_DIR);
			} catch (final IOException e) {
				e.printStackTrace();
			}
		}
	}

	private static boolean isAllowed(final Set<String> allowedPrograms, final Set<File> programRevisions) {
		if (allowedPrograms.isEmpty()) {
			return true;
		}
		for (final File programRevision : programRevisions) {
			final String parentDirAndName =
					programRevision.getParentFile().getName() + "\\" + programRevision.getName();
			if (allowedPrograms.contains(parentDirAndName)) {
				return true;
			}
		}
		return false;
	}

	private static Set<String> getAllowedPrograms(final String fullpath) {
		try {
			return new HashSet<>(CoreUtil.readFileLineByLine(fullpath));
		} catch (final IOException ex) {
			System.err.println("Could not get list of allowed programs, allowing all");
			return Collections.emptySet();
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

		final Comparator<File> numericComparator = new Comparator<File>() {
			@Override
			public int compare(final File o1, final File o2) {
				final String revStr1 = o1.getName().substring(0, 3);
				final String revStr2 = o2.getName().substring(0, 3);
				return Integer.compare(Integer.parseInt(revStr1), Integer.parseInt(revStr2));
			}
		};
		final Map<String, TreeSet<File>> program2ListOfRevisions = new TreeMap<>();
		final File rootDir = new File(fullPath);
		final Iterator<File> dirIter = Arrays.stream(rootDir.list((file, name) -> file.isDirectory()))
				.map(a -> new File(rootDir, a)).iterator();
		while (dirIter.hasNext()) {
			final File currentDir = dirIter.next();
			// the dir name is the name of the program
			// the files there are named <revnumber>.<hash>.<file/kernel>.cil_<expectedresult>.<fileext>

			final File[] dirContent = currentDir.listFiles();
			if (dirContent == null) {
				continue;
			}
			for (final File file : dirContent) {
				final String filename = file.getName();
				if (!filename.endsWith(".i") && !filename.endsWith(".c")) {
					continue;
				}

				final String[] filenameparts = filename.split("\\.");
				if (filenameparts.length < 3) {
					System.err.println("Unknown naming for " + filename);
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
		CoreUtil.deleteDirectory(ATS_DUMP_DIR);
		// TestUtil.deleteDirectoryContentsIf(new File(TestUtil.getPathFromTrunk(BENCHMARK_DIR)),
		// file -> !file.isDirectory() && file.getName().endsWith(".ats"));
	}
}
