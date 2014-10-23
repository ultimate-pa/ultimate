package de.uni_freiburg.informatik.ultimatetest.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.util.Utils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.SafetyCheckerOverallResult;
import de.uni_freiburg.informatik.ultimatetest.decider.overallResult.TerminationAnalysisOverallResult;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestLogfile;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class Util {

	private static String sPlatformLineSeparator = System.getProperty("line.separator");

	public static String getPlatformLineSeparator() {
		return sPlatformLineSeparator;
	}

	public static String readFile(File file) throws IOException {
		return readFile(file.getAbsolutePath());
	}

	public static String readFile(String filename) throws IOException {
		BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(new File(filename)), "UTF8"));
		try {

			StringBuilder sb = new StringBuilder();
			String line = br.readLine();
			while (line != null) {
				sb.append(line);
				sb.append(sPlatformLineSeparator);
				line = br.readLine();
			}
			return sb.toString();
		} finally {
			br.close();
		}
	}

	public static void writeFile(String filename, String[] content) throws IOException {

		File outputFile = new File(filename);
		outputFile.createNewFile();

		Writer out = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(outputFile), "UTF-8"));
		try {
			for (String s : content) {
				out.write(s);
				out.write(sPlatformLineSeparator);
			}

		} finally {
			out.close();
		}
	}

	/**
	 * Generates a name based on the current time, the original name of the
	 * input file and the description string such that it should be unique and
	 * recognizable.
	 * 
	 * @param inputFile
	 *            An instance representing a file on the local machine
	 * @param description
	 *            A description for the log file name.
	 * @return A string representing the absolute path to a file on the local
	 *         machine.
	 */
	public static String generateLogFilename(File inputFile, String description) {

		DateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd-HH-mm-ss");

		String dir = inputFile.getParent() + File.separator;

		String originalFileName = inputFile.getName();

		String name = "UltimateTest ";
		if (description != null && description.length() > 0) {
			name = name + description + "_";
		}

		name = name + originalFileName + "_" + dateFormat.format(Calendar.getInstance().getTime()) + ".log";
		name = name.replaceAll(" ", "_");
		return dir + name;
	}

	/**
	 * Combines a relative path with the base directory of this plugin, i.e. you
	 * can say getPathFromHere("../../examples/settings/") to reach the setting
	 * directory
	 * 
	 * @param path
	 *            A string representing a relative path. Please use "/" as path
	 *            separator regardless of OS. Java will recognize \\, but this
	 *            wont work under Linux
	 * @return A string representing the absolute path to the relative path
	 *         based on the actual position of this package
	 */
	public static String getPathFromHere(String path) {
		File here = new File(System.getProperty("user.dir"));
		File relative = new File(here.getAbsolutePath() + File.separator + path);
		return relative.getAbsolutePath();
	}

	public static String getPathFromSurefire(String path, String canonicalClassName) {
		File trunk = new File(System.getProperty("user.dir"));
		File relative = new File(trunk.getAbsolutePath() + File.separator + "target" + File.separator
				+ "surefire-reports" + File.separator + canonicalClassName + File.separator + path);

		return relative.getAbsolutePath();
	}

	public static String getPathFromTrunk(String path) {
		File trunk = new File(System.getProperty("user.dir")).getParentFile().getParentFile();
		File relative = new File(trunk.getAbsolutePath() + File.separator + path);
		return relative.getAbsolutePath();
	}

	/**
	 * Returns all elements of a collection that match the check defined by
	 * predicate.
	 * 
	 * @param collection
	 *            The collection you want to filter. May not be null.
	 * @param predicate
	 *            The predicate you want to use to filter said collection. May
	 *            not be null.
	 * @return A new collection that only contains elements for which
	 *         {@link IPredicate#check(Object)} returned true.
	 */
	public static <E> Collection<E> where(Collection<E> collection, IPredicate<E> predicate) {
		ArrayList<E> rtr = new ArrayList<>();
		for (E entry : collection) {
			if (predicate.check(entry)) {
				rtr.add(entry);
			}
		}
		return rtr;
	}

	/**
	 * Returns a {@link Set} of elements that are created by applying the
	 * reducer to every element in the collection.
	 * 
	 * @param collection
	 *            May not be null.
	 * @param reducer
	 *            May not be null.
	 * @return
	 */
	public static <T, E> Set<T> selectDistinct(Collection<E> collection, IReduce<T, E> reducer) {
		Set<T> rtr = new HashSet<>();
		for (E entry : collection) {
			rtr.add(reducer.reduce(entry));
		}
		return rtr;
	}
	
	public static <T, E> Collection<T> select(Collection<E> collection, IReduce<T, E> reducer) {
		Collection<T> rtr = new ArrayList<>();
		for (E entry : collection) {
			rtr.add(reducer.reduce(entry));
		}
		return rtr;
	}

	public static <T, E> T reduce(Collection<E> collection, IMapReduce<T, E> reducer) {
		T lastValue = null;
		for (E entry : collection) {
			lastValue = reducer.reduce(lastValue, entry);
		}
		return lastValue;
	}

	/***
	 * Filters a list of files based on a given regex. Returns a collection of
	 * files of which the path matches the regex.
	 * 
	 * @param files
	 * @param regex
	 * @return
	 */
	public static Collection<File> filterFiles(Collection<File> files, String regex) {
		ArrayList<File> singleFiles = new ArrayList<File>();

		for (File f : files) {
			String path = f.getAbsolutePath().replaceAll("\\\\", "/");
			if (path.matches(regex)) {
				singleFiles.add(f);
			}
		}

		return singleFiles;
	}

	/**
	 * Get absolute path for the file in which an ITestLogfile will be written.
	 * This includes also the filename.
	 */
	public static String generateAbsolutePathForLogfile(ITestLogfile testSummary) {
		String absolutPath = Util.getPathFromSurefire(generateLogfilename(testSummary), testSummary
				.getUltimateTestSuiteClass().getCanonicalName());
		return absolutPath;
	}

	/**
	 * Get filename for the file in which an ITestSummary will be written.
	 * Returns only the name of the file without directories.
	 */
	private static String generateLogfilename(ITestLogfile testSummary) {
		String filename = testSummary.getDescriptiveLogName() + " " + getCurrentDateTimeAsString()
				+ testSummary.getFilenameExtension();
		return filename;
	}

	public static String getCurrentDateTimeAsString() {
		return new SimpleDateFormat("yyyy-MM-dd_HH-mm-ss-SSS").format(Calendar.getInstance().getTime());
	}

	public static String generateLogfilename(String directory, String description) {
		if (description == null) {
			description = "";
		}

		if (description.length() > 0) {
			description = description + " ";
		}

		File f = new File(directory);

		String dir = "";
		if (f.isDirectory()) {
			dir = f + File.separator;
		} else {
			dir = f.getParent() + File.separator;
		}
		String name = "UltimateTest Summary " + description + getCurrentDateTimeAsString() + ".log";

		return dir + name;
	}

	public static Collection<File> getFiles(File root, String[] endings) {
		ArrayList<File> rtr = new ArrayList<File>();

		if (root.isFile()) {
			rtr.add(root);
			return rtr;
		}

		File[] list = root.listFiles();

		if (list == null) {
			return rtr;
		}

		for (File f : list) {
			if (f.isDirectory()) {
				rtr.addAll(getFiles(f, endings));
			} else {

				if (endings == null || endings.length == 0) {
					rtr.add(f);
				} else {
					for (String s : endings) {
						if (f.getAbsolutePath().endsWith(s)) {
							rtr.add(f);
							break;
						}

					}
				}
			}
		}
		return rtr;
	}

	/**
	 * Returns recursively all files in a directory that have a path which is
	 * matched by regex. If root is a file, a collection containing root is
	 * returned (ignoring the regex)
	 * 
	 * @param root
	 * @param regex
	 * @return
	 */
	public static Collection<File> getFilesRegex(File root, String[] regex) {
		ArrayList<File> rtr = new ArrayList<File>();

		if (root.isFile()) {
			rtr.add(root);
			return rtr;
		}

		File[] list = root.listFiles();

		if (list == null) {
			return rtr;
		}

		for (File f : list) {
			if (f.isDirectory()) {
				rtr.addAll(getFilesRegex(f, regex));
			} else {

				if (regex == null || regex.length == 0) {
					rtr.add(f);
				} else {
					for (String s : regex) {
						try {
							if (f.getAbsolutePath().matches(s)) {
								rtr.add(f);
								break;
							}
						} catch (Exception e) {

						}

					}
				}
			}
		}
		return rtr;
	}

	public static <E> Collection<E> firstN(Collection<E> collection, int n) {
		ArrayList<E> rtr = new ArrayList<E>(n);
		int i = 1;
		for (E elem : collection) {
			rtr.add(elem);
			++i;
			if (n < i) {
				break;
			}
		}
		return rtr;
	}

	public static <E> Collection<E> uniformN(Collection<E> collection, int n) {
		ArrayList<E> rtr = new ArrayList<E>(n);
		int i = 1;
		int size = collection.size();
		int step = 1;
		if (n != 0) {
			step = (int) Math.floor(((double) size) / ((double) n));
		}

		for (E elem : collection) {
			if (i % step == 0) {
				rtr.add(elem);
			}
			++i;
		}
		return rtr;
	}

	/**
	 * 
	 * @param logger
	 * @param inputFile
	 * @param fail
	 * @param customMessages
	 */
	public static void logResults(final Logger logger, String inputFile, boolean fail,
			Collection<String> customMessages, IResultService resultService) {

		if (logger == null) {
			logResults(new ILogWriter() {
				@Override
				public void write(String message) {
					System.err.println(message);
				}
			}, inputFile, fail, customMessages, resultService);
		} else {
			logResults(new ILogWriter() {
				@Override
				public void write(String message) {
					logger.info(message);
				}
			}, inputFile, fail, customMessages, resultService);
		}
	}

	private static void logResults(ILogWriter logger, String inputFile, boolean fail,
			Collection<String> customMessages, IResultService resultService) {
		logger.write("#################### TEST RESULT ####################");
		logger.write("Results for " + inputFile);

		if (resultService == null) {
			logger.write("There is no IResultService (this indicates that Ultimate terminated abnormally");
		} else {

			for (Entry<String, List<IResult>> entry : resultService.getResults().entrySet()) {
				int i = 0;
				for (IResult result : entry.getValue()) {
					logger.write(String.format("[%s] %s --> [%s] %s", i, entry.getKey(), result.getClass()
							.getSimpleName(), result.getLongDescription()));
					++i;
				}
			}
		}

		if (customMessages != null && customMessages.size() > 0) {
			for (String s : customMessages) {
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
		long heapSize = Runtime.getRuntime().totalMemory();

		// Get amount of free memory within the heap in bytes. This size will
		// increase // after garbage collection and decrease as new objects are
		// created.
		long heapFreeSize = Runtime.getRuntime().freeMemory();

		// Get maximum size of heap in bytes. The heap cannot grow beyond this
		// size.// Any attempt will result in an OutOfMemoryException.
		long heapMaxSize = Runtime.getRuntime().maxMemory();

		logger.write(String.format("Statistics: heapSize=%s heapFreeSize=%s heapMaxSize=%s",
				Utils.humanReadableByteCount(heapSize, true), Utils.humanReadableByteCount(heapFreeSize, true),
				Utils.humanReadableByteCount(heapMaxSize, true)));

		logger.write("#################### END TEST RESULT ####################");
	}

	private interface ILogWriter {
		public void write(String message);
	}

	/**
	 * Returns a map from keywords to verification results. We use keywords in
	 * filenames to specify expected verification results. If a key of this map
	 * is a substring of the filename, the value of this map is the expected
	 * verification result of a safety checker.
	 */
	public static Map<String, SafetyCheckerOverallResult> constructFilenameKeywordMap_SafetyChecker() {
		Map<String, SafetyCheckerOverallResult> map = new HashMap<String, SafetyCheckerOverallResult>();
		map.put("-safe", SafetyCheckerOverallResult.SAFE);
		map.put("_safe", SafetyCheckerOverallResult.SAFE);
		map.put("-Safe", SafetyCheckerOverallResult.SAFE);
		map.put("_Safe", SafetyCheckerOverallResult.SAFE);
		map.put("-unsafe", SafetyCheckerOverallResult.UNSAFE);
		map.put("_unsafe", SafetyCheckerOverallResult.UNSAFE);
		map.put("-Unsafe", SafetyCheckerOverallResult.UNSAFE);
		map.put("_Unsafe", SafetyCheckerOverallResult.UNSAFE);
		// true-unreach-call is the SV-COMP annotation for safe
		map.put("_true-unreach-call", SafetyCheckerOverallResult.SAFE);
		// false-unreach-call is the SV-COMP annotation for safe
		map.put("_false-unreach-call", SafetyCheckerOverallResult.UNSAFE);
		// true-valid-memsafety is the SV-COMP annotation for safe wrt. memory safety
		map.put("_true-valid-memsafety", SafetyCheckerOverallResult.SAFE);
		// false-valid-deref is the SV-COMP annotation for unsafe wrt. pointer dereference
		map.put("_false-valid-deref", SafetyCheckerOverallResult.UNSAFE_DEREF);
		// false-valid-free is the SV-COMP annotation for unsafe wrt. free
		map.put("_false-valid-free", SafetyCheckerOverallResult.UNSAFE_FREE);
		// false-valid-memtrack is the SV-COMP annotation for unsafe wrt. memory leaks
		map.put("_false-valid-memtrack", SafetyCheckerOverallResult.UNSAFE_MEMTRACK);
		return map;
	}

	/**
	 * Returns a map from keywords to verification results. We use keywords in
	 * the first line of files to specify expected verification results. If a
	 * key of this map is a substring of the first line, the value of this map
	 * is the expected verification result of a safety checker.
	 */
	public static Map<String, SafetyCheckerOverallResult> constructFirstlineKeywordMap_SafetyChecker() {
		Map<String, SafetyCheckerOverallResult> map = new HashMap<String, SafetyCheckerOverallResult>();
		map.put("#Safe", SafetyCheckerOverallResult.SAFE);
		map.put("#Unsafe", SafetyCheckerOverallResult.UNSAFE);
		map.put("#SyntaxError", SafetyCheckerOverallResult.SYNTAX_ERROR);
		return map;
	}

	/**
	 * Returns a map from keywords to verification results. We use keywords in
	 * filenames to specify expected verification results. If a key of this map
	 * is a substring of the filename, the value of this map is the expected
	 * verification result of a termination analysis.
	 */
	public static Map<String, TerminationAnalysisOverallResult> constructFilenameKeywordMap_TerminationAnalysis() {
		Map<String, TerminationAnalysisOverallResult> map = new HashMap<String, TerminationAnalysisOverallResult>();
		// true-unreach-call is the SV-COMP annotation for safe
		map.put("_true-termination", TerminationAnalysisOverallResult.TERMINATING);
		// false-unreach-call is the SV-COMP annotation for safe
		map.put("_false-termination", TerminationAnalysisOverallResult.NONTERMINATING);
		return map;
	}

	/**
	 * Returns a map from keywords to verification results. We use keywords in
	 * the first line of files to specify expected verification results. If a
	 * key of this map is a substring of the first line, the value of this map
	 * is the expected verification result of a termination analysis.
	 */
	public static Map<String, TerminationAnalysisOverallResult> constructFirstlineKeywordMap_TerminationAnalysis() {
		Map<String, TerminationAnalysisOverallResult> map = new HashMap<String, TerminationAnalysisOverallResult>();
		map.put("#rTerminationDerivable", TerminationAnalysisOverallResult.TERMINATING);
		map.put("#rTermination", TerminationAnalysisOverallResult.TERMINATING);
		map.put("#rNonTerminationDerivable", TerminationAnalysisOverallResult.NONTERMINATING);
		map.put("#rNonTermination", TerminationAnalysisOverallResult.NONTERMINATING);
		map.put("#SyntaxError", TerminationAnalysisOverallResult.SYNTAX_ERROR);
		return map;
	}

	/**
	 * Returns the first line of File file as String.
	 */
	public static String extractFirstLine(File file) {
		BufferedReader br;
		String line = null;
		try {
			br = new BufferedReader(new FileReader(file));
			line = br.readLine();
			br.close();
		} catch (IOException e) {
			throw new AssertionError("unable to read file " + file);
		}
		return line;
	}

	/**
	 * Returns new Collections that contains all IResults from ultimateIResults
	 * that are subclasses of the class resClass.
	 */
	public static <E extends IResult> Collection<E> filterResults(Map<String, List<IResult>> ultimateIResults,
			Class<E> resClass) {
		ArrayList<E> filteredList = new ArrayList<E>();
		for (Entry<String, List<IResult>> entry : ultimateIResults.entrySet()) {
			for (IResult res : entry.getValue()) {
				if (res.getClass().isAssignableFrom(resClass)) {
					@SuppressWarnings("unchecked")
					E benchmarkResult = (E) res;
					filteredList.add((E) benchmarkResult);
				}
			}
		}
		return filteredList;
	}

	/**
	 * Returns all ICsvProviderProvider of class benchmarkClass that are stored
	 * in the BenchmarkResults benchmarkResults.
	 */
	@SuppressWarnings("rawtypes")
	private static <E extends ICsvProviderProvider> Collection<E> getCsvProviderProviderFromBenchmarkResults(
			Collection<BenchmarkResult> benchmarkResults, Class<E> benchmarkClass) {
		ArrayList<E> filteredList = new ArrayList<E>();
		for (BenchmarkResult<?> benchmarkResult : benchmarkResults) {
			@SuppressWarnings("unchecked")
			E benchmark = (E) benchmarkResult.getBenchmark();
			if (benchmark.getClass().isAssignableFrom(benchmarkClass)) {
				filteredList.add(benchmark);
			}
		}
		return filteredList;
	}

	/**
	 * Returns all ICsvProviderProvider of class benchmarkClass that are stored
	 * in the BenchmarkResults of ultimateIResults.
	 */
	@SuppressWarnings("rawtypes")
	public static <E extends ICsvProviderProvider<?>> Collection<E> getCsvProviderProviderFromUltimateResults(
			Map<String, List<IResult>> ultimateIResults, Class<E> benchmarkClass) {
		Collection<BenchmarkResult> benchmarks = filterResults(ultimateIResults, BenchmarkResult.class);
		return getCsvProviderProviderFromBenchmarkResults(benchmarks, benchmarkClass);
	}

	/**
	 * Returns an absolute path to the SVCOMP root directory specified by the
	 * Maven variable "svcompdir". If there is no variable with such a name, the
	 * parameter fallback will be used. The method converts relative paths to
	 * absolute ones.
	 * 
	 * @param fallback
	 *            A string describing a relative or absolute path to an existing
	 *            directory (which is hopefully the SVCOMP root directory).
	 * @return An absolute path to an existing directory or null
	 */
	public static String getFromMavenVariableSVCOMPRoot(String fallback) {
		String svcompDir = makeAbsolutePath(System.getProperty("svcompdir"));
		if (svcompDir != null) {
			return svcompDir;
		}

		svcompDir = makeAbsolutePath(fallback);
		return svcompDir;
	}

	/**
	 * Converts a relative path to an absolute one and checks if this path
	 * exists.
	 * 
	 * @param somepath
	 *            A relative or absolute path
	 * @return An absolute path to an existing file or directory or null
	 */
	public static String makeAbsolutePath(String somepath) {
		if (somepath == null) {
			return null;
		}
		File path = new File(somepath);
		if (!path.isAbsolute()) {
			path = new File(Util.getPathFromTrunk(path.getPath()));
		}
		if (path.exists()) {
			return path.getAbsolutePath();
		} else {
			return null;
		}
	}

	/**
	 * Indents a (possibly multiline) String such that the resulting
	 * StringBuilder object contains the same String, but indented with the
	 * indentPrefix. It also converts line breaks to the system-specific line
	 * separator.
	 * 
	 * @param original
	 * @param indentPrefix
	 * @param forceRemoveLastLinebreak
	 *            When true, the last linebreak will always be removed, when
	 *            false, an existing last line break will be preserved (but
	 *            converted to system-specific line break)
	 * @return
	 */
	public static StringBuilder indentMultilineString(String original, String indentPrefix,
			boolean forceRemoveLastLinebreak) {
		StringBuilder sb = new StringBuilder();
		String lineSeparator = System.getProperty("line.separator");
		String[] splitted = original.split("\\r?\\n");

		for (String s : splitted) {
			sb.append(indentPrefix).append(s).append(lineSeparator);
		}

		char last = original.charAt(original.length() - 1);
		if (forceRemoveLastLinebreak || (last != '\n' && last != '\r')) {
			sb.replace(sb.length() - lineSeparator.length(), sb.length(), "");
		}
		return sb;
	}

	/**
	 * Flattens a string, i.e. removes all line breaks and replaces them with
	 * separator
	 * 
	 * @param original
	 * @param separator
	 * @return
	 */
	public static StringBuilder flatten(String original, String separator) {
		StringBuilder sb = new StringBuilder();
		String[] splitted = original.split("\\r?\\n");
		for (String s : splitted) {
			sb.append(s).append(separator);
		}
		sb.replace(sb.length() - separator.length(), sb.length(), "");
		return sb;
	}

	public static void writeSummary(ITestSummary testSummary) {
		File logFile = new File(Util.generateAbsolutePathForLogfile(testSummary));

		if (!logFile.isDirectory()) {
			logFile.getParentFile().mkdirs();
		}

		String summaryLog = testSummary.getSummaryLog().trim();
		if (summaryLog == null || summaryLog.isEmpty()) {
			return;
		}

		try {
			FileWriter fw = new FileWriter(logFile);
			Logger.getLogger(testSummary.getUltimateTestSuiteClass()).info(
					"Writing " + testSummary.getDescriptiveLogName() + " for "
							+ testSummary.getUltimateTestSuiteClass().getCanonicalName() + " to "
							+ logFile.getAbsolutePath());
			fw.write(summaryLog);
			fw.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public interface IReduce<T, K> {
		public T reduce(K entry);
	}

	public interface IMapReduce<T, K> {
		public T reduce(T lastValue, K entry);
	}

	public interface IPredicate<T> {
		public boolean check(T entry);
	}

}
