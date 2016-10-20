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
 *
 */
public final class PlotUtil {
	/**
	 * The name for plot data CSV files.
	 */
	public static final String FILE_NAME_PLOT_DATA_CSV = "plotData.csv";

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

		BufferedReader br = null;
		PrintWriter pw = null;
		try {
			br = new BufferedReader(new FileReader(benchmarkPlotFile));
			pw = new PrintWriter(
					new FileWriter(new File(benchmarkPlotFile.getParentFile(), FILE_NAME_PLOT_DATA_CSV)));
			final String[] headers = br.readLine().split(separator);

			int directoryIndex = -1;
			int sizeIndex = -1;
			int removedIndex = -1;
			for (int i = 0; i < headers.length; i++) {
				final String header = headers[i];
				if (header.equals("DIRECTORY")) {
					directoryIndex = i;
				} else if (header.equals(ECountingMeasure.BUCHI_STATES.toString())) {
					sizeIndex = i;
				} else if (header.equals(ECountingMeasure.REMOVED_STATES.toString())) {
					removedIndex = i;
				}
			}

			pw.println("INTERNAL_DENSITY" + separator + "CALL_DENSITY" + separator + "RETURN_DENSITY" + separator
					+ "HIERPRED_DENSITY" + separator + "SIZE" + separator + "REMOVED" + separator + "ACCEPTANCE");

			while (br.ready()) {
				final String line = br.readLine();
				if (line == null) {
					break;
				}

				final String[] values = line.split(separator);
				final String directory = values[directoryIndex];
				final String sizeText = values[sizeIndex];
				final String removedText = values[removedIndex];

				final int size;
				if (sizeText.equals(noValue)) {
					size = 0;
				} else {
					size = Integer.parseInt(sizeText);
				}
				final int removed;
				if (removedText.equals(noValue)) {
					removed = 0;
				} else {
					removed = Integer.parseInt(removedText);
				}

				int acceptance = -1;
				int internalDensity = -1;
				int callDensity = -1;
				int returnDensity = -1;
				int hierPredDensity = -1;
				Pattern directoryPattern = Pattern.compile(
						".*#\\d+_n\\d+_k\\d+_f(\\d+)(?:\\.\\d+)?%_ti(\\d+)(?:\\.\\d+)?%_tc(\\d+)(?:\\.\\d+)?%_tr(\\d+)(?:\\.\\d+)?%_th(\\d+)(?:\\.\\d+)?%$");
				Matcher directoryMatcher = directoryPattern.matcher(directory);
				if (directoryMatcher.find()) {
					acceptance = Integer.parseInt(directoryMatcher.group(1));
					internalDensity = Integer.parseInt(directoryMatcher.group(2));
					callDensity = Integer.parseInt(directoryMatcher.group(3));
					returnDensity = Integer.parseInt(directoryMatcher.group(4));
					hierPredDensity = Integer.parseInt(directoryMatcher.group(5));
				} else {
					System.out.println(directory);
					throw new IllegalStateException();
				}

				pw.println(internalDensity + separator + callDensity + separator + returnDensity + separator
						+ hierPredDensity + separator + size + separator + removed + separator + acceptance);
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

	/**
	 * Utility class. No implementation.
	 */
	private PlotUtil() {

	}
}
