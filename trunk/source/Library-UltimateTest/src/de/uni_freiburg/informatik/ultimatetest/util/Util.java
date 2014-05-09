package de.uni_freiburg.informatik.ultimatetest.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Random;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.util.Utils;

public class Util {

	public static String readFile(File file) throws IOException {
		return readFile(file.getAbsolutePath());
	}

	public static String readFile(String filename) throws IOException {
		BufferedReader br = new BufferedReader(new FileReader(filename));
		try {
			StringBuilder sb = new StringBuilder();
			String line = br.readLine();

			while (line != null) {
				sb.append(line);
				sb.append("\n");
				line = br.readLine();
			}
			return sb.toString();
		} finally {
			br.close();
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

	/***
	 * Filters a list of files based on a given regex. Returns a collection of
	 * files of which the path matches the regex.
	 * 
	 * @param files
	 * @param regex
	 * @return
	 */
	public static Collection<File> filter(Collection<File> files, String regex) {
		ArrayList<File> singleFiles = new ArrayList<File>();

		for (File f : files) {
			String path = f.getAbsolutePath().replaceAll("\\\\", "/");
			if (path.matches(regex)) {
				singleFiles.add(f);
			}
		}

		return singleFiles;
	}

	public static String generateSummaryLogFilename(String directory, String description) {
		DateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd-HH-mm-ss-SSS");

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
		String name = "UltimateTest Summary " + description + dateFormat.format(Calendar.getInstance().getTime())
				+ ".log";

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
	public static void logResults(Logger logger, String inputFile, boolean fail, Collection<String> customMessages) {

		logger.info("#################### TEST RESULT ####################");
		logger.info("Results for " + inputFile);

		for (Entry<String, List<IResult>> entry : UltimateServices.getInstance().getResultMap().entrySet()) {
			int i = 0;
			for (IResult result : entry.getValue()) {
				logger.info(String.format("[%s] %s --> [%s] %s", i, entry.getKey(), result.getClass().getSimpleName(),
						result.getLongDescription()));
				++i;
			}
		}

		if (customMessages != null && customMessages.size() > 0) {
			for (String s : customMessages) {
				if (s != null) {
					logger.info(s);
				}
			}
		}

		if (fail) {
			logger.info("TEST FAILED");
		} else {
			logger.info("TEST SUCCEEDED");
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

		logger.info(String.format("Statistics: heapSize=%s heapFreeSize=%s heapMaxSize=%s",
				Utils.humanReadableByteCount(heapSize, true), Utils.humanReadableByteCount(heapFreeSize, true),
				Utils.humanReadableByteCount(heapMaxSize, true)));

		logger.info("#################### END TEST RESULT ####################");
	}

	/**
	 * Result that we expect after checking filename and keywords of the input
	 * file.
	 */
	public enum ExpectedResult {
		SAFE, UNSAFE, SYNTAXERROR, NOANNOTATION
	}

	/**
	 * Read the expected result from the current input file.
	 * 
	 * Expected results are expected to be specified in an input file's first
	 * line and start with '//#Unsafe', '//#Safe' or '//#SyntaxError'. If this
	 * is not case, the expected result may be specified within the file name
	 * via the suffix "-safe" or "-unsafe".
	 */
	public static ExpectedResult getExpectedResult(File inputFile) {
		BufferedReader br;
		String line = null;
		try {
			br = new BufferedReader(new FileReader(inputFile));
			line = br.readLine();
			br.close();
		} catch (IOException e) {
			line = null;
		}
		if (line != null) {
			if (line.contains("#Safe")) {
				return ExpectedResult.SAFE;
			} else if (line.contains("#Unsafe")) {
				return ExpectedResult.UNSAFE;
			} else if (line.contains("#SyntaxError")) {
				return ExpectedResult.SYNTAXERROR;
			}
		}
		if (inputFile.getName().toLowerCase().contains("-safe") 
				|| inputFile.getName().toLowerCase().contains("_safe")
				// true-unreach-call is the SV-COMP annotation for safe
				|| inputFile.getName().toLowerCase().contains("true-unreach-call")){
			return ExpectedResult.SAFE;
		} else if (inputFile.getName().toLowerCase().contains("-unsafe")
				|| inputFile.getName().toLowerCase().contains("_unsafe")
				// false-unreach-call is the SV-COMP annotation for safe
				|| inputFile.getName().toLowerCase().contains("false-unreach-call")){
			return ExpectedResult.UNSAFE;
		}
		return ExpectedResult.NOANNOTATION;
	}

	/**
	 * Returns new Collections that contains all IResults from resCollection
	 * that are subclasses of the class resClass.
	 */
	public static <E extends IResult> Collection<E> filterResults(Collection<IResult> resCollection, Class<E> resClass) {
		ArrayList<E> filteredList = new ArrayList<E>();
		for (IResult res : resCollection) {
			if (res.getClass().isAssignableFrom(resClass)) {
				@SuppressWarnings("unchecked")
				E benchmarkResult = (E) res;
				filteredList.add((E) benchmarkResult);
			}
		}
		return filteredList;
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
}
