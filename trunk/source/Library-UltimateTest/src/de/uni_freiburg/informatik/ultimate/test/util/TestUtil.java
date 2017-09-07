/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.test.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.SafetyCheckerOverallResult;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.TerminationAnalysisOverallResult;
import de.uni_freiburg.informatik.ultimate.test.reporting.INonIncrementalLog;
import de.uni_freiburg.informatik.ultimate.test.reporting.ITestLogfile;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class TestUtil {

	private static final long PSEUDO_RANDOM_FILE_SELECTION_SEED = 19120623;

	private TestUtil() {
		// utility classes should not be instantiated
	}

	/**
	 * Select (n - offset) files from a collection of files in a pseudo-random and deterministic way.
	 */
	public static Collection<File> limitFiles(final Collection<File> files, final int offset, final int n) {
		if (files == null || n == 0) {
			return Collections.emptyList();
		} else if (files.isEmpty() || n < 0) {
			return files;
		} else if (offset >= files.size()) {
			return Collections.emptyList();
		} else if (offset == 0 && n >= files.size()) {
			return files;
		} else {
			final List<File> shuffle = new ArrayList<>(files);
			Collections.shuffle(shuffle, new Random(PSEUDO_RANDOM_FILE_SELECTION_SEED));
			int nPlusOffset;
			if ((long) offset + (long) n > Integer.MAX_VALUE) {
				nPlusOffset = Integer.MAX_VALUE;
			} else {
				nPlusOffset = offset + n;
			}
			final int upperIndex = Math.min(files.size(), nPlusOffset);
			return new ArrayList<>(shuffle.subList(offset, upperIndex));
		}
	}

	/**
	 * Generates a name based on the current time, the original name of the input file and the description string such
	 * that it should be unique and recognizable.
	 *
	 * @param inputFile
	 *            An instance representing a file on the local machine
	 * @param description
	 *            A description for the log file name.
	 * @return A string representing the absolute path to a file on the local machine.
	 */
	public static String generateLogFilename(final File inputFile, final String description) {
		final DateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd-HH-mm-ss");
		final String dir = inputFile.getParent() + File.separator;
		final String originalFileName = inputFile.getName();

		String name = "UltimateTest ";
		if (description != null && description.length() > 0) {
			name = name + description + "_";
		}

		name = name + originalFileName + "_" + dateFormat.format(Calendar.getInstance().getTime()) + ".log";
		name = name.replaceAll(" ", "_");
		return dir + name;
	}

	/**
	 * Combines a relative path with the base directory of this plugin, i.e. you can say
	 * getPathFromHere("../../examples/settings/") to reach the setting directory
	 *
	 * @param path
	 *            A string representing a relative path. Please use "/" as path separator regardless of OS. Java will
	 *            recognize \\, but this wont work under Linux
	 * @return A string representing the absolute path to the relative path based on the actual position of this package
	 */
	public static String getPathFromHere(final String path) {
		final File here = new File(System.getProperty("user.dir"));
		final File relative = new File(here.getAbsolutePath() + File.separator + path);
		return relative.getAbsolutePath();
	}

	public static String getPathFromSurefire(final String path, final String canonicalClassName) {
		final File trunk = new File(System.getProperty("user.dir"));
		final File relative = new File(trunk.getAbsolutePath() + File.separator + "target" + File.separator
				+ "surefire-reports" + File.separator + canonicalClassName + File.separator + path);

		return relative.getAbsolutePath();
	}

	/**
	 * Prefix the parameter "path" with the path to the trunk folder of the Ultimate repository on the current machine.
	 *
	 * @param path
	 * @return
	 */
	public static String getPathFromTrunk(final String path) {
		final File trunk = new File(System.getProperty("user.dir")).getParentFile().getParentFile();
		final File relative = new File(trunk.getAbsolutePath() + File.separator + path);
		if (!relative.exists()) {
			throw new IllegalArgumentException("Path " + relative.getAbsolutePath() + " does not exist.");
		}
		return relative.getAbsolutePath();
	}

	public static String removeTrunkExamplesPrefix(final String path) {
		final String trunk = TestUtil.getPathFromTrunk("");
		final String examples = trunk + File.separator + "examples" + File.separator;
		final int lastIndexOf = path.lastIndexOf(examples);
		if (lastIndexOf != -1) {
			final String trunkated = path.substring(lastIndexOf + examples.length(), path.length());
			return trunkated;
		}
		return path;
	}

	public static String removeTrunkSettingsPrefix(final String path) {
		final String trunk = TestUtil.getPathFromTrunk("");
		final String examples = trunk + File.separator + "examples" + File.separator + "settings" + File.separator;
		final int lastIndexOf = path.lastIndexOf(examples);
		if (lastIndexOf != -1) {
			final String trunkated = path.substring(lastIndexOf + examples.length(), path.length());
			return trunkated;
		}
		return path;
	}

	public static String removeTrunkToolchainPrefix(final String path) {
		final String trunk = TestUtil.getPathFromTrunk("");
		final String examples = trunk + File.separator + "examples" + File.separator + "toolchains" + File.separator;
		final int lastIndexOf = path.lastIndexOf(examples);
		if (lastIndexOf != -1) {
			final String trunkated = path.substring(lastIndexOf + examples.length(), path.length());
			return trunkated;
		}
		return path;
	}

	/***
	 * Filters a list of files based on a given regex. Returns a collection of files of which the path matches the
	 * regex.
	 *
	 * @param files
	 * @param regex
	 * @return
	 */
	public static Collection<File> filterFiles(final Collection<File> files, final String regex) {
		final ArrayList<File> singleFiles = new ArrayList<>();

		for (final File f : files) {
			final String path = f.getAbsolutePath();
			if (path.matches(regex)) {
				singleFiles.add(f);
			}
		}

		return singleFiles;
	}

	/**
	 * Get absolute path for the file in which an ITestLogfile will be written. This includes also the filename.
	 */
	public static String generateAbsolutePathForLogfile(final ITestLogfile testSummary) {
		final String absolutPath = TestUtil.getPathFromSurefire(generateLogfilename(testSummary),
				testSummary.getUltimateTestSuiteClass().getCanonicalName());
		return absolutPath;
	}

	/**
	 * Get filename for the file in which an ITestSummary will be written. Returns only the name of the file without
	 * directories.
	 */
	public static String generateLogfilename(final ITestLogfile testSummary) {
		final String filename = testSummary.getDescriptiveLogName() + "_"
				+ de.uni_freiburg.informatik.ultimate.util.CoreUtil.getCurrentDateTimeAsString()
				+ testSummary.getFilenameExtension();
		return filename;
	}

	public static String generateLogfilename(final String directory, String description) {
		if (description == null) {
			description = "";
		}

		if (description.length() > 0) {
			description = description + " ";
		}

		final File f = new File(directory);

		String dir = "";
		if (f.isDirectory()) {
			dir = f + File.separator;
		} else {
			dir = f.getParent() + File.separator;
		}
		final String name = "UltimateTest Summary " + description
				+ de.uni_freiburg.informatik.ultimate.util.CoreUtil.getCurrentDateTimeAsString() + ".log";

		return dir + name;
	}

	public static String getRegexFromFileendings(final String[] fileendings) {
		if (fileendings == null || fileendings.length == 0) {
			return ".*";
		}
		final StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append("\\").append(fileendings[0]);
		for (int i = 1; i < fileendings.length; i++) {
			sb.append("|\\").append(fileendings[i]);
		}
		sb.append(")$");
		return sb.toString();
	}

	public static List<File> getFiles(final File root, final String... endings) {
		final List<File> rtr = new ArrayList<>();

		if (root.isFile()) {
			for (final String s : endings) {
				if (root.getAbsolutePath().endsWith(s)) {
					rtr.add(root);
					break;
				}
			}
			return rtr;
		}

		final File[] list = root.listFiles();
		if (list == null) {
			return rtr;
		}

		for (final File f : list) {
			rtr.addAll(getFiles(f, endings));
		}
		return rtr;
	}

	public static Predicate<File> getFileEndingTest(final String... endings) {
		return file -> {
			if (!file.isFile()) {
				return false;
			}
			final String abspath = file.getAbsolutePath();
			for (final String s : endings) {
				if (abspath.endsWith(s)) {
					return true;
				}
			}
			return false;
		};
	}

	public static Predicate<File> getRegexTest(final String... regexes) {
		return file -> file != null && Arrays.stream(regexes).allMatch(regex -> file.getAbsolutePath().matches(regex));
	}

	public static Predicate<File> getRegexTest(final Collection<String> regexes) {
		return file -> file != null && regexes.stream().allMatch(regex -> file.getAbsolutePath().matches(regex));
	}

	/**
	 * Returns recursively all files in a directory that have a path whose suffix beyond root is matched by regex. If
	 * root is a file, a collection containing root is returned (ignoring the regex) E.g., your file root has the
	 * absolute path /home/horst/ultimate/ and your regex is *horst* you obtain the files that contain the String
	 * "horst" if the prefix "/home/horst/ultimate/" was removed.
	 *
	 * @param root
	 * @param regex
	 * @return
	 */
	public static Collection<File> getFilesRegex(final File root, final String[] regex) {
		return getFilesRegex(root.getAbsolutePath(), root, regex);
	}

	/**
	 * Returns recursively all files in a directory that have a path whose suffix beyond the String prefix is matched by
	 * regex. If root is a file, a collection containing root is returned (ignoring the regex).
	 *
	 * @param root
	 * @param regex
	 * @return
	 */
	private static Collection<File> getFilesRegex(final String prefix, final File root, final String[] regex) {
		if (!root.getAbsolutePath().startsWith(prefix)) {
			throw new IllegalArgumentException("prefix is no prefix of root.getAbsolutePath()");
		}
		final List<File> rtr = new ArrayList<>();

		if (root.isFile()) {
			rtr.add(root);
			return rtr;
		}

		final File[] list = root.listFiles();

		if (list == null) {
			return rtr;
		}

		for (final File f : list) {
			if (f.isDirectory()) {
				rtr.addAll(getFilesRegex(prefix, f, regex));
			} else if (regex == null || regex.length == 0) {
				rtr.add(f);
			} else {
				for (final String s : regex) {
					final String suffix = f.getAbsolutePath().substring(prefix.length());
					if (suffix.matches(s)) {
						rtr.add(f);
						break;
					}
				}
			}
		}
		return rtr;
	}

	public static <E> Collection<E> uniformN(final Collection<E> collection, final int n) {
		final List<E> rtr = new ArrayList<>(n);
		final int size = collection.size();

		int step = 1;
		if (n != 0) {
			step = (int) Math.floor((double) size / (double) n);
		}

		int i = 1;
		for (final E elem : collection) {
			if (i % step == 0) {
				rtr.add(elem);
			}
			++i;
		}
		return rtr;
	}

	public static void logResults(final Class<?> caller, final String inputFile, final boolean fail,
			final Collection<String> customMessages, final IUltimateServiceProvider services) {
		final ILogger logger = services.getLoggingService().getLogger(caller);
		logResults(logger, inputFile, fail, customMessages, services.getResultService());
	}

	public static void logResults(final ILogger logger, final String inputFile, final boolean fail,
			final Collection<String> customMessages, final IResultService resultService) {

		if (logger == null) {
			logResults(message -> System.err.println(message), inputFile, fail, customMessages, resultService);
		} else {
			logResults(message -> logger.info(message), inputFile, fail, customMessages, resultService);
		}
	}

	private static void logResults(final ILogWriter logger, final String inputFile, final boolean fail,
			final Collection<String> customMessages, final IResultService resultService) {
		logger.write("#################### TEST RESULT ####################");
		logger.write("Results for " + inputFile);

		if (resultService == null) {
			logger.write("There is no IResultService (this indicates that Ultimate terminated abnormally");
		} else {

			for (final Entry<String, List<IResult>> entry : resultService.getResults().entrySet()) {
				int i = 0;
				for (final IResult result : entry.getValue()) {
					logger.write(String.format("[%s] %s --> [%s] %s", i, entry.getKey(),
							result.getClass().getSimpleName(), result.getLongDescription()));
					++i;
				}
			}
		}

		if (customMessages != null && !customMessages.isEmpty()) {
			for (final String s : customMessages) {
				if (s != null) {
					logger.write(s);
				}
			}
		}

		if (fail) {
			logger.write("TEST FAILED");
		} else {
			logger.write("TEST SUCCEEDED");
		}

		// Get current size of heap in bytes
		final long heapSize = Runtime.getRuntime().totalMemory();

		// Get amount of free memory within the heap in bytes. This size will
		// increase // after garbage collection and decrease as new objects are
		// created.
		final long heapFreeSize = Runtime.getRuntime().freeMemory();

		// Get maximum size of heap in bytes. The heap cannot grow beyond this
		// size.// Any attempt will result in an OutOfMemoryException.
		final long heapMaxSize = Runtime.getRuntime().maxMemory();

		logger.write(String.format("Statistics: heapSize=%s heapFreeSize=%s heapMaxSize=%s",
				CoreUtil.humanReadableByteCount(heapSize, true), CoreUtil.humanReadableByteCount(heapFreeSize, true),
				CoreUtil.humanReadableByteCount(heapMaxSize, true)));

		logger.write("#################### END TEST RESULT ####################");
	}

	/**
	 * Returns a map from keywords to verification results. We use keywords in filenames to specify expected
	 * verification results. If a key of this map is a substring of the filename, the value of this map is the expected
	 * verification result of a safety checker.
	 */
	public static Map<String, SafetyCheckerOverallResult> constructFilenameKeywordMap_AllSafetyChecker() {
		final Map<String, SafetyCheckerOverallResult> map = new HashMap<>();
		map.put(".*-safe.*", SafetyCheckerOverallResult.SAFE);
		map.put(".*_safe.*", SafetyCheckerOverallResult.SAFE);
		map.put(".*-Safe.*", SafetyCheckerOverallResult.SAFE);
		map.put(".*_Safe.*", SafetyCheckerOverallResult.SAFE);
		map.put(".*-unsafe.*", SafetyCheckerOverallResult.UNSAFE);
		map.put(".*_unsafe.*?!(.*_false-valid-deref.*)", SafetyCheckerOverallResult.UNSAFE);
		map.put(".*-Unsafe.*", SafetyCheckerOverallResult.UNSAFE);
		map.put(".*_Unsafe.*", SafetyCheckerOverallResult.UNSAFE);
		map.putAll(constructFilenameKeywordMap_SvcompReach());
		map.putAll(constructFilenameKeywordMap_SvcompMemsafety());
		map.putAll(constructFilenameKeywordMap_SvcompOverflow());
		return map;
	}

	/**
	 * Returns a map from SV-COMP filename keywords to verification results for the error function reachability
	 * specification.
	 */
	public static Map<String, SafetyCheckerOverallResult> constructFilenameKeywordMap_SvcompReach() {
		final Map<String, SafetyCheckerOverallResult> map = new HashMap<>();
		// true-unreach-call is the SV-COMP annotation for safe wrt. reachability of error function
		map.put(".*_true-unreach-call.*", SafetyCheckerOverallResult.SAFE);
		// false-unreach-call is the SV-COMP annotation for unsafe wrt. reachability of error function
		map.put(".*_false-unreach-call.*", SafetyCheckerOverallResult.UNSAFE);
		return map;
	}

	/**
	 * Returns a map from SV-COMP filename keywords to verification results for memsafety specification.
	 */
	public static Map<String, SafetyCheckerOverallResult> constructFilenameKeywordMap_SvcompMemsafety() {
		final Map<String, SafetyCheckerOverallResult> map = new HashMap<>();
		map.put(".*_true-valid-memsafety.*", SafetyCheckerOverallResult.SAFE);
		// false-valid-deref is the SV-COMP annotation for unsafe wrt. pointer
		// dereference
		map.put(".*_false-valid-deref.*", SafetyCheckerOverallResult.UNSAFE_DEREF);
		// false-valid-free is the SV-COMP annotation for unsafe wrt. free
		map.put(".*_false-valid-free.*", SafetyCheckerOverallResult.UNSAFE_FREE);
		// false-valid-memtrack is the SV-COMP annotation for unsafe wrt. memory
		// leaks
		map.put(".*_false-valid-memtrack.*", SafetyCheckerOverallResult.UNSAFE_MEMTRACK);
		return map;
	}

	/**
	 * Returns a map from SV-COMP filename keywords to verification results for overflow specification.
	 */
	public static Map<String, SafetyCheckerOverallResult> constructFilenameKeywordMap_SvcompOverflow() {
		final Map<String, SafetyCheckerOverallResult> map = new HashMap<>();
		// no-overflow is SV-COMP annotation for signed integer overflows
		map.put(".*_true-no-overflow.*", SafetyCheckerOverallResult.SAFE);
		map.put(".*_false-no-overflow.*", SafetyCheckerOverallResult.UNSAFE);
		return map;
	}

	/**
	 * Returns a map from keywords to verification results. We use keywords in the first line of files to specify
	 * expected verification results. If a key of this map is a substring of the first line, the value of this map is
	 * the expected verification result of a safety checker.
	 */
	public static Map<String, SafetyCheckerOverallResult> constructFirstlineKeywordMap_SafetyChecker() {
		final Map<String, SafetyCheckerOverallResult> map = new HashMap<>();
		map.put("#Safe", SafetyCheckerOverallResult.SAFE);
		map.put("#Unsafe", SafetyCheckerOverallResult.UNSAFE);
		map.put("#SyntaxError", SafetyCheckerOverallResult.SYNTAX_ERROR);
		// we use the following two keywords for concurrent programs
		map.put("#cSafe", SafetyCheckerOverallResult.SAFE);
		map.put("#cUnsafe", SafetyCheckerOverallResult.UNSAFE);
		return map;
	}

	public static Map<String, SafetyCheckerOverallResult> constructFirstlineKeywordMapUnknownSafetyChecker() {
		final Map<String, SafetyCheckerOverallResult> map = new HashMap<>();
		map.putAll(constructFirstlineKeywordMap_SafetyChecker());
		map.put("#Unknown", SafetyCheckerOverallResult.UNKNOWN);
		return map;
	}

	/**
	 * Returns a map from keywords to verification results. We use keywords in filenames to specify expected
	 * verification results. If a key of this map is a substring of the filename, the value of this map is the expected
	 * verification result of a termination analysis.
	 */
	public static Map<String, TerminationAnalysisOverallResult> constructFilenameKeywordMap_TerminationAnalysis() {
		final Map<String, TerminationAnalysisOverallResult> map = new HashMap<>();
		// true-unreach-call is the SV-COMP annotation for safe
		map.put(".*_true-termination.*", TerminationAnalysisOverallResult.TERMINATING);
		// false-unreach-call is the SV-COMP annotation for safe
		map.put(".*_false-termination.*", TerminationAnalysisOverallResult.NONTERMINATING);
		return map;
	}

	/**
	 * Returns a map from keywords to verification results. We use keywords in paths to specify expected verification
	 * results. If a key of this map is a substring of the path, the value of this map is the expected verification
	 * result of a termination analysis.
	 */
	public static Map<String, TerminationAnalysisOverallResult> constructPathKeywordMap_TerminationAnalysis() {
		final Map<String, TerminationAnalysisOverallResult> map = new HashMap<>();
		// we sometimes put terminating examples in a folder with this name
		map.put("/terminating", TerminationAnalysisOverallResult.TERMINATING);
		// we sometimes put nonterminating examples in a folder with this name
		map.put("/nonterminating", TerminationAnalysisOverallResult.NONTERMINATING);
		return map;
	}

	/**
	 * Returns a map from keywords to verification results. We use keywords in the first line of files to specify
	 * expected verification results. If a key of this map is a substring of the first line, the value of this map is
	 * the expected verification result of a termination analysis.
	 */
	public static Map<String, TerminationAnalysisOverallResult> constructFirstlineKeywordMap_TerminationAnalysis() {
		final Map<String, TerminationAnalysisOverallResult> map = new HashMap<>();
		map.put("#rTerminationDerivable", TerminationAnalysisOverallResult.TERMINATING);
		map.put("#rTermination", TerminationAnalysisOverallResult.TERMINATING);
		map.put("#Terminating", TerminationAnalysisOverallResult.TERMINATING);
		map.put("#rNonTerminationDerivable", TerminationAnalysisOverallResult.NONTERMINATING);
		map.put("#rNonTermination", TerminationAnalysisOverallResult.NONTERMINATING);
		map.put("#Nonterminating", TerminationAnalysisOverallResult.NONTERMINATING);
		map.put("#SyntaxError", TerminationAnalysisOverallResult.SYNTAX_ERROR);
		return map;
	}
	
	/**
	 * Returns a map from keywords to verification results. We use keywords in the first line of files to specify
	 * expected verification results. If a key of this map is a substring of the first line, the value of this map is
	 * the expected verification result of a termination analysis.
	 */
	public static Map<String, TerminationAnalysisOverallResult> constructFirstlineKeywordMap_Termcomp2016() {
		final Map<String, TerminationAnalysisOverallResult> map = new HashMap<>();
		map.put("#termcomp16-someonesaidyes", TerminationAnalysisOverallResult.TERMINATING);
		map.put("#termcomp16-someonesaidno", TerminationAnalysisOverallResult.NONTERMINATING);
		return map;
	}

	/**
	 * Returns the first line of File file as String.
	 */
	public static String extractFirstLine(final File file) {
		BufferedReader br;
		String line = null;
		try {
			br = new BufferedReader(new FileReader(file));
			line = br.readLine();
			br.close();
		} catch (final IOException e) {
			throw new AssertionError("unable to read file " + file);
		}
		return line;
	}
	
	/**
	 * Returns the line of File file that starts with "(set-info :status", or null if there is no such line
	 */
	public static String extractSMTLibStatusInfo(final File file) {
		BufferedReader br;
		String line = null;
		try {
			br = new BufferedReader(new FileReader(file));
			while (true) {
				line = br.readLine();
				if (line.trim().startsWith("(set-info :status")) {
					// found the status
					br.close();
					break;
				}
				if (line.trim().startsWith("(assert")) {
					// found an assert before the status information --> file does not seem to contain status info
					br.close();
					return null;
				}
			}
		} catch (final IOException e) {
			throw new AssertionError("unable to read file " + file);
		}
		return line;
	}
	

	/**
	 * Returns an absolute path to the SVCOMP root directory specified by the Maven variable "svcompdir". If there is no
	 * variable with such a name, the parameter fallback will be used. The method converts relative paths to absolute
	 * ones.
	 *
	 * @param fallback
	 *            A string describing a relative or absolute path to an existing directory (which is hopefully the
	 *            SVCOMP root directory).
	 * @return An absolute path to an existing directory or null
	 */
	public static String getFromMavenVariableSVCOMPRoot(final String fallback) {
		String svcompDir = makeAbsolutePath(System.getProperty("svcompdir"));
		if (svcompDir != null) {
			return svcompDir;
		}

		svcompDir = makeAbsolutePath(fallback);
		return svcompDir;
	}

	/**
	 * Converts a relative path to an absolute one and checks if this path exists.
	 *
	 * @param somepath
	 *            A relative or absolute path
	 * @return An absolute path to an existing file or directory or null
	 */
	public static String makeAbsolutePath(final String somepath) {
		if (somepath == null) {
			return null;
		}
		File path = new File(somepath);
		if (!path.isAbsolute()) {
			path = new File(TestUtil.getPathFromTrunk(path.getPath()));
		}
		if (path.exists()) {
			return path.getAbsolutePath();
		}
		return null;
	}

	public static void writeNonIncrementalLog(final INonIncrementalLog nonIncrementalLog, final ILogger logger) {
		final File logFile = new File(TestUtil.generateAbsolutePathForLogfile(nonIncrementalLog));
		if (!logFile.isDirectory()) {
			if (!logFile.getParentFile().mkdirs()) {
				if (!logFile.getParentFile().isDirectory()) {
					logger.warn("Did not create parent directory: " + logFile.getParentFile());
				}
			}
		}

		final String summaryLog = nonIncrementalLog.getLog().trim();
		if (summaryLog == null || summaryLog.isEmpty()) {
			logger.warn(nonIncrementalLog.getClass() + " is empty");
			return;
		}

		try {
			final FileWriter writer = new FileWriter(logFile);
			logger.info("Writing " + nonIncrementalLog.getDescriptiveLogName() + " for "
					+ nonIncrementalLog.getUltimateTestSuiteClass().getCanonicalName() + " to "
					+ logFile.getAbsolutePath());
			writer.write(summaryLog);
			writer.close();
		} catch (final IOException e) {
			logger.fatal("Exception while writing to " + logFile.getAbsolutePath(), e);
		}
	}

	/**
	 * The JUnit view in Eclipse seems to limit the length of the test case name to a certain length. You cannot rerun
	 * tests in the GUI if two test cases have the same prefix. This methods tries to reduce the length of the string
	 * representing a test case name such that this limit is not reached.
	 *
	 * @param testCaseName
	 *            The original test case name.
	 * @return The minimized test case name.
	 */
	public static String minimizeTestCaseName(final String testCaseName) {
		if (null == testCaseName) {
			return null;
		}
		String rtr = testCaseName;
		rtr = rtr.replaceAll("Input:", "I:");
		rtr = rtr.replaceAll("Settings:", "S:");
		rtr = rtr.replaceAll("Toolchain:", "T:");
		rtr = rtr.replaceAll("Toolchain:", "T:");

		if (rtr.length() > 255) {
			final String currentSuffix = String.valueOf(rtr.hashCode());
			rtr = rtr.substring(0, 254 - currentSuffix.length());
			rtr = rtr + "-" + currentSuffix;
		}

		return rtr;
	}

	private interface ILogWriter {
		public void write(String message);
	}
}
