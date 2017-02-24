package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ESimulationType;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Provides utility methods for converting benchmark data provided by the Rabit
 * tool to formats used by Ultimates simulation benchmark framework.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public final class RabitUtil {
	/**
	 * File representing the working environment.
	 */
	public static final File ENVIRONMENT =
			new File(new File(System.getProperty("user.home"), "Desktop"), "RabitTestEnvironment");
	/**
	 * File representing the directory containing the automata.
	 */
	public static final File FILE_AUTOMATA = new File(ENVIRONMENT, "automata");
	/**
	 * File extension to filter for.
	 */
	public static final String FILE_EXTENSION_FILTER = "ba";
	/**
	 * File representing the output.
	 */
	public static final File FILE_OUTPUT = new File(ENVIRONMENT, "testData.tsv");
	/**
	 * After how many processed automata a logging message should be printed.
	 */
	public static final int LOG_EVERY = 5;
	/**
	 * The maximal heap size in gigabyte to use for the Rabit tool.
	 */
	public static final int MAX_HEAP_SIZE_GB = 14;
	/**
	 * The minimal heap size in gigabyte to use for the Rabit tool.
	 */
	public static final int MIN_HEAP_SIZE_GB = 2;
	/**
	 * The separator used by the Rabit tool for its output.
	 */
	public static final String RABIT_SEPARATOR = " ";
	/**
	 * The separator used in the output file.
	 */
	public static final String SEPARATOR = "\t";
	/**
	 * Name of the tool to use.
	 */
	public static final String TOOL = "Reduce_test.jar";

	private RabitUtil() {
		// utility class
	}

	/**
	 * Appends the given content to the output file.
	 * 
	 * @param content
	 *            The content to append to the output
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public static void appendLineToOutput(final String content) throws IOException {
		appendToFile(FILE_OUTPUT, content);
	}

	/**
	 * Collects all the automata to process.
	 * 
	 * @return A list of automata to process
	 */
	public static List<File> collectAutomata() {
		final List<File> collectedAutomata = new LinkedList<>();
		listFiles(FILE_AUTOMATA, collectedAutomata, FILE_EXTENSION_FILTER);
		return collectedAutomata;
	}

	/**
	 * Executes the Rabit tool on a given automaton using the given arguments.
	 * 
	 * @param automaton
	 *            Automaton to execute Rabit on
	 * @param arguments
	 *            Arguments to pass to the Rabit tool
	 * @return The standard output produced by the tool
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public static List<String> executeRabit(final File automaton, final String arguments) throws IOException {
		final Runtime rt = Runtime.getRuntime();
		String command = "java";
		command += " -Xms" + MIN_HEAP_SIZE_GB + "g -Xms" + MIN_HEAP_SIZE_GB + "G";
		command += " -Xmx" + MAX_HEAP_SIZE_GB + "g -Xmx" + MAX_HEAP_SIZE_GB + "G";
		command += " -jar";
		command += " " + TOOL;
		command += " \"" + automaton.getAbsolutePath() + "\"";
		command += " " + arguments;
		final Process proc = rt.exec(command, null, ENVIRONMENT);

		final BufferedReader rabitOutput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
		final BufferedReader rabitError = new BufferedReader(new InputStreamReader(proc.getErrorStream()));

		String s = null;
		final List<String> outputLines = new LinkedList<>();
		while ((s = rabitOutput.readLine()) != null) {
			outputLines.add(s);
		}

		final List<String> errorLines = new LinkedList<>();
		while ((s = rabitError.readLine()) != null) {
			errorLines.add(s);
		}

		if (!errorLines.isEmpty()) {
			throw new IllegalStateException("Error in Rabit tool: " + errorLines);
		}

		return outputLines;
	}

	/**
	 * Collects all BA-automata from a given directory, executes the RABIT tool
	 * on them and finally aggregates and converts the results to a format used
	 * by Ultimate.
	 * 
	 * @param args
	 *            Not supported
	 * @throws IOException
	 *             If an I/O-Exception occurred.
	 */
	public static void main(final String[] args) throws IOException {
		System.out.println("Start");

		// The list of commands to execute with Rabit and
		// representing names of them
		final List<Pair<String, ESimulationType>> commands = new LinkedList<>();
		commands.add(new Pair<>("1 -light", ESimulationType.EXT_RABIT_LIGHT_1));
		commands.add(new Pair<>("1 -heavy", ESimulationType.EXT_RABIT_HEAVY_1));

		// Collect all automata
		final List<File> automataToProcess = collectAutomata();

		// Process all automata
		int automataToGo = automataToProcess.size();
		for (final File automaton : automataToProcess) {
			processAutomaton(automaton, commands);

			// Log message
			automataToGo--;
			if (automataToGo % LOG_EVERY == 0) {
				System.out.println("\tAutomata to go: " + automataToGo);
			}
		}

		System.out.println("Terminated");
	}

	/**
	 * Processes the given automaton by executing the Rabit tool with all given
	 * commands and saving the output to a file.
	 * 
	 * @param automaton
	 *            The automaton to process
	 * @param commands
	 *            A list of Rabit tool commands with each pair having the
	 *            argument to pass and a name for the argument
	 */
	public static void processAutomaton(final File automaton, final List<Pair<String, ESimulationType>> commands)
			throws IOException {
		// Print header
		String header = "<!--";
		// Fix fields
		header += SEPARATOR + "NAME";
		header += SEPARATOR + "TYPE";
		header += SEPARATOR + "USED_SCCS";
		header += SEPARATOR + "TIMED_OUT";
		header += SEPARATOR + "OOM";
		// Variable fields
		header += SEPARATOR + ETimeMeasure.OVERALL;
		header += SEPARATOR + ECountingMeasure.BUCHI_ALPHABET_SIZE;
		header += SEPARATOR + ECountingMeasure.BUCHI_STATES;
		header += SEPARATOR + ECountingMeasure.BUCHI_TRANSITIONS;
		header += SEPARATOR + ECountingMeasure.BUCHI_TRANSITIONS_INTERNAL;
		header += SEPARATOR + ECountingMeasure.RESULT_ALPHABET_SIZE;
		header += SEPARATOR + ECountingMeasure.RESULT_STATES;
		header += SEPARATOR + ECountingMeasure.RESULT_TRANSITIONS;
		header += SEPARATOR + ECountingMeasure.RESULT_TRANSITIONS_INTERNAL;
		header += SEPARATOR + ECountingMeasure.REMOVED_STATES;
		header += SEPARATOR + "-->";
		appendLineToOutput(header);

		for (final Pair<String, ESimulationType> command : commands) {
			final String commandArguments = command.getFirst();
			final ESimulationType commandName = command.getSecond();

			// Execute the command
			final List<String> output = executeRabit(automaton, commandArguments);

			if (output.size() != 1) {
				throw new IllegalStateException("Expected Rabit output to only have one line: " + output);
			}

			// Save the output
			final String[] outputData = output.iterator().next().split(RABIT_SEPARATOR);

			final int rabitNameIndex = 0;
			final int rabitBuchiStatesIndex = 1;
			final int rabitBuchiTransitionsIndex = 2;
			final int rabitBuchiAlphabetSizeIndex = 3;
			final int rabitResultStatesIndex = 5;
			final int rabitResultTransitionsIndex = 6;
			final int rabitResultAlphabetSizeIndex = 7;
			final int rabitOverallTime = 9;

			String line = "";
			// Fix fields
			line += outputData[rabitNameIndex];
			line += SEPARATOR + commandName;
			line += SEPARATOR + new Boolean(false).booleanValue();
			line += SEPARATOR + new Boolean(false).booleanValue();
			line += SEPARATOR + new Boolean(false).booleanValue();
			// Variable fields
			line += SEPARATOR + ComparisonTables.millisToSeconds(Long.parseLong(outputData[rabitOverallTime]));
			line += SEPARATOR + outputData[rabitBuchiAlphabetSizeIndex];
			line += SEPARATOR + outputData[rabitBuchiStatesIndex];
			line += SEPARATOR + outputData[rabitBuchiTransitionsIndex];
			line += SEPARATOR + outputData[rabitBuchiTransitionsIndex];
			line += SEPARATOR + outputData[rabitResultAlphabetSizeIndex];
			line += SEPARATOR + outputData[rabitResultStatesIndex];
			line += SEPARATOR + outputData[rabitResultTransitionsIndex];
			line += SEPARATOR + outputData[rabitResultTransitionsIndex];
			line += SEPARATOR + (Integer.parseInt(outputData[rabitBuchiStatesIndex])
					- Integer.parseInt(outputData[rabitResultStatesIndex]));
			appendLineToOutput(line);
		}
	}

	/**
	 * Appends the given content to the given file.
	 * 
	 * @param file
	 *            The file to write to
	 * @param content
	 *            The content to append to the file
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	private static void appendToFile(final File file, final String content) throws IOException {
		final PrintWriter pw = new PrintWriter(new FileWriter(file, true));
		pw.println(content);
		pw.close();
	}

	/**
	 * Lists all files in the given directory and all sub-directories by adding
	 * them to the given list.
	 * 
	 * @param directory
	 *            The directory to list all files of
	 * @param files
	 *            The list to add the found files
	 * @param extensionFilter
	 *            The extension to filter for
	 */
	private static void listFiles(final File directory, final List<File> files, final String extensionFilter) {
		final File[] fileList = directory.listFiles();
		for (final File file : fileList) {
			if (file.isFile() && stripExtension(file.getName())[1].equals(extensionFilter)) {
				files.add(file);
			} else if (file.isDirectory()) {
				listFiles(file, files, extensionFilter);
			}
		}
	}

	/**
	 * Strips the extension of a given file name.
	 * 
	 * @param fileName
	 *            File name to strip the extension
	 * @return
	 *         <ul>
	 *         <li>[0] - The file name without the extension</li>
	 *         <li>[1] - The extension itself, empty if there is no</li>
	 *         </ul>
	 *         or <tt>null</tt> if the given file name is <tt>null</tt>
	 */
	private static String[] stripExtension(final String fileName) {
		if (fileName == null) {
			return null;
		}

		final String[] result = new String[2];

		final int pos = fileName.lastIndexOf('.');

		if (pos == -1) {
			result[0] = fileName;
			result[1] = "";
		} else {
			result[0] = fileName.substring(0, pos);
			result[1] = fileName.substring(pos + 1, fileName.length());
		}

		return result;
	}
}
