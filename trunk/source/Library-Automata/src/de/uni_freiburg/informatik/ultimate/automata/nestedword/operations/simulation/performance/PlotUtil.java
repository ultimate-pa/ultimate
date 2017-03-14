package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Provides utility methods for plotting performance entry tables.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public final class PlotUtil {
	/**
	 * The name for plot data CSV files.
	 */
	public static final String FILE_NAME_PLOT_DATA_CSV = "plotData.csv";

	private PlotUtil() {
		// utility class
	}

	/**
	 * Demonstrates the usage of the plot utlity class.
	 * 
	 * @param args
	 *            Not supported
	 * @throws IOException
	 *             If an I/O-Exception occurred.
	 */
	public static void main(final String[] args) throws IOException {
		System.out.println("Start");
		final File path = CompareReduceBuchiSimulation.LOG_PATH;
		writeBenchmarkPlotToTransitionDensityCsv(new File(path, "plot_averagedSimulationPerDirectoryTable.csv"));
		System.out.println("Terminated");
	}

	/**
	 * Reads a given benchmark file in the plot format and writes the benchmark
	 * data to a CSV file next to it containing the transition densities and
	 * benchmark data.
	 * 
	 * @param benchmarkPlotFile
	 *            The file to read
	 * @throws IOException
	 *             If an I/O-Exception occurred.
	 */
	public static void writeBenchmarkPlotToTransitionDensityCsv(final File benchmarkPlotFile) throws IOException {
		final String separator = CompareReduceBuchiSimulation.PLOT_SEPARATOR;
		final String noValue = CompareReduceBuchiSimulation.PLOT_NO_VALUE;

		// Skips stuff like call and return transition data
		final boolean skipNwaStuff = true;
		// Skips trying to read data from directory name
		final boolean skipDirectoryNameExtraction = false;

		BufferedReader br = null;
		PrintWriter pw = null;
		try {
			br = new BufferedReader(new FileReader(benchmarkPlotFile));
			pw = new PrintWriter(new FileWriter(new File(benchmarkPlotFile.getParentFile(), FILE_NAME_PLOT_DATA_CSV)));
			final String[] headers = br.readLine().split(separator);

			int directoryIndex = -1;
			int internalAfterPreProcIndex = -1;
			int callAfterPreProcIndex = -1;
			int returnAfterPreProcIndex = -1;
			int internalOutputIndex = -1;
			int callOutputIndex = -1;
			int returnOutputIndex = -1;
			int sizeAfterPreProcIndex = -1;
			int removedIndex = -1;
			int overallTimeIndex = -1;
			for (int i = 0; i < headers.length; i++) {
				final String header = headers[i];
				if (header.equals("DIRECTORY")) {
					directoryIndex = i;
				} else if (header.equals(CountingMeasure.BUCHI_TRANSITIONS_INTERNAL.toString())) {
					internalAfterPreProcIndex = i;
				} else if (header.equals(CountingMeasure.BUCHI_TRANSITIONS_CALL.toString())) {
					callAfterPreProcIndex = i;
				} else if (header.equals(CountingMeasure.BUCHI_TRANSITIONS_RETURN.toString())) {
					returnAfterPreProcIndex = i;
				} else if (header.equals(CountingMeasure.RESULT_TRANSITIONS_INTERNAL.toString())) {
					internalOutputIndex = i;
				} else if (header.equals(CountingMeasure.RESULT_TRANSITIONS_CALL.toString())) {
					callOutputIndex = i;
				} else if (header.equals(CountingMeasure.RESULT_TRANSITIONS_RETURN.toString())) {
					returnOutputIndex = i;
				} else if (header.equals(CountingMeasure.BUCHI_STATES.toString())) {
					sizeAfterPreProcIndex = i;
				} else if (header.equals(CountingMeasure.REMOVED_STATES.toString())) {
					removedIndex = i;
				} else if (header.equals(TimeMeasure.OVERALL.toString())) {
					overallTimeIndex = i;
				}
			}

			pw.println("INTERNAL_DENSITY" + separator + "CALL_DENSITY" + separator + "RETURN_DENSITY" + separator
					+ "HIERPRED_DENSITY" + separator + "ACCEPTANCE" + separator + "#INTERNAL_AFTER_PRE_PROC" + separator
					+ "#CALL_AFTER_PRE_PROC" + separator + "#RETURN_AFTER_PRE_PROC" + separator + "#INTERNAL_OUTPUT"
					+ separator + "#CALL_OUTPUT" + separator + "#RETURN_OUTPUT" + separator + "SIZE_INITIAL" + separator
					+ "SIZE_AFTER_PRE_PROC" + separator + "SIZE_OUTPUT" + separator + "OVERALL_TIME");

			while (br.ready()) {
				final String line = br.readLine();
				if (line == null) {
					break;
				}

				final String[] values = line.split(separator);
				final String directory = values[directoryIndex];
				final String internalAfterPreProcText = values[internalAfterPreProcIndex];
				final String internalOutputText = values[internalOutputIndex];

				final String callAfterPreProcText;
				final String returnAfterPreProcText;
				final String callOutputText;
				final String returnOutputText;
				if (skipNwaStuff) {
					callAfterPreProcText = noValue;
					returnAfterPreProcText = noValue;
					callOutputText = noValue;
					returnOutputText = noValue;
				} else {
					callAfterPreProcText = values[callAfterPreProcIndex];
					returnAfterPreProcText = values[returnAfterPreProcIndex];
					callOutputText = values[callOutputIndex];
					returnOutputText = values[returnOutputIndex];
				}

				final String sizeAfterPreProcText = values[sizeAfterPreProcIndex];
				final String removedText = values[removedIndex];
				final String overallTimeText = values[overallTimeIndex];

				final int internalAfterPreProc;
				if (internalAfterPreProcText.equals(noValue)) {
					internalAfterPreProc = 0;
				} else {
					internalAfterPreProc = Integer.parseInt(internalAfterPreProcText);
				}
				final int callAfterPreProc;
				if (callAfterPreProcText.equals(noValue)) {
					callAfterPreProc = 0;
				} else {
					callAfterPreProc = Integer.parseInt(callAfterPreProcText);
				}
				final int returnAfterPreProc;
				if (returnAfterPreProcText.equals(noValue)) {
					returnAfterPreProc = 0;
				} else {
					returnAfterPreProc = Integer.parseInt(returnAfterPreProcText);
				}
				final int internalOutput;
				if (internalOutputText.equals(noValue)) {
					internalOutput = 0;
				} else {
					internalOutput = Integer.parseInt(internalOutputText);
				}
				final int callOutput;
				if (callOutputText.equals(noValue)) {
					callOutput = 0;
				} else {
					callOutput = Integer.parseInt(callOutputText);
				}
				final int returnOutput;
				if (returnOutputText.equals(noValue)) {
					returnOutput = 0;
				} else {
					returnOutput = Integer.parseInt(returnOutputText);
				}
				final int sizeAfterPreProc;
				if (sizeAfterPreProcText.equals(noValue)) {
					sizeAfterPreProc = 0;
				} else {
					sizeAfterPreProc = Integer.parseInt(sizeAfterPreProcText);
				}
				final int removed;
				if (removedText.equals(noValue)) {
					removed = 0;
				} else {
					removed = Integer.parseInt(removedText);
				}
				final int sizeOutput = sizeAfterPreProc - removed;
				final float overallTimeOutput;
				if (overallTimeText.equals(noValue)) {
					overallTimeOutput = 0;
				} else {
					overallTimeOutput = Float.parseFloat(overallTimeText);
				}

				int sizeInitial = -1;
				int acceptance = -1;
				int internalDensity = -1;
				int callDensity = -1;
				int returnDensity = -1;
				int hierPredDensity = -1;
				final Pattern directoryPattern = Pattern.compile(
						".*#\\d+_n(\\d+)_k\\d+_f(\\d+)(?:\\.\\d+)?%_ti(\\d+)(?:\\.\\d+)?%_tc(\\d+)(?:\\.\\d+)?%_tr(\\d+)(?:\\.\\d+)?%_th(\\d+)(?:\\.\\d+)?%$");
				final Matcher directoryMatcher = directoryPattern.matcher(directory);
				if (!skipDirectoryNameExtraction) {
					if (directoryMatcher.find()) {
						sizeInitial = Integer.parseInt(directoryMatcher.group(1));
						acceptance = Integer.parseInt(directoryMatcher.group(2));
						internalDensity = Integer.parseInt(directoryMatcher.group(3));
						callDensity = Integer.parseInt(directoryMatcher.group(4));
						returnDensity = Integer.parseInt(directoryMatcher.group(5));
						hierPredDensity = Integer.parseInt(directoryMatcher.group(6));
					} else {
						System.out.println(directory);
						throw new IllegalStateException();
					}
				}

				pw.println(internalDensity + separator + callDensity + separator + returnDensity + separator
						+ hierPredDensity + separator + acceptance + separator + internalAfterPreProc + separator
						+ callAfterPreProc + separator + returnAfterPreProc + separator + internalOutput + separator
						+ callOutput + separator + returnOutput + separator + sizeInitial + separator + sizeAfterPreProc
						+ separator + sizeOutput + separator + overallTimeOutput);
			}
		} finally {
			if (br != null) {
				br.close();
			}
			if (pw != null) {
				pw.close();
			}
		}
	}
}
