package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.function.Consumer;
import java.util.stream.Collectors;

/**
 * Measures speed of different closures on matrices from Benchmark set.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class ClosureBenchmark {

	public static void main(String[] args) {
		ClosureBenchmark cb = new ClosureBenchmark("/tmp/empty");
		cb.addCandidate("naiv", OctMatrix::shortestPathClosureNaiv);
		cb.addCandidate("apron", OctMatrix::shortestPathClosureApron);
		cb.addCandidate("fsparse", OctMatrix::shortestPathClosureFullSparse);
		cb.addCandidate("sparse", OctMatrix::shortestPathClosureSparse);
		cb.addCandidate("psparse", OctMatrix::shortestPathClosurePrimitiveSparse);
		cb.run(3);
		cb.printFullStatistics();
		cb.printShortStatistics(8);
		cb.printResults();
	}
	
	////////////////////////////////////////////////////////////////

	/** Candidate to attend the benchmark. */
	private static class Candidate {
		
		/** Human-readable name of the closure variant. */
		String name;

		/** Function which calculates the shortest path closure (in-place). */
		Consumer<OctMatrix> closureAlgorithm;
		
		/** Measured time in ns from last scenario. */
		long measuredNanoSeconds;
	}
	
	private static class MatrixStatistic {
		
		/** Number of variables in this matrix. */
		int variables;
		
		/** Infinity values / total number of values in block lower matrix. */
		double infinityPercentageInBlockLowerHalf;
		
		boolean isBottom;
		boolean isBottomInt;
	}
	
	////////////////////////////////////////////////////////////////
	
	
	private final Path mBenchmarkDirectory;
	private final List<Candidate> mCandidates;
	private final List<MatrixStatistic> mMatrixStatistics;
	private final long mProgressInfoIntervalInNanoSeconds = 30_000_000_000L; // 30 seconds
	
	public ClosureBenchmark(String benchmarkDirectory) {
		mBenchmarkDirectory = Paths.get(benchmarkDirectory);
		mCandidates = new ArrayList<>();
		mMatrixStatistics = new ArrayList<>();
	}
	
	public void addCandidate(String name, Consumer<OctMatrix> closureAlgorithm) {
		Candidate c = new Candidate();
		c.name = name;
		c.closureAlgorithm = closureAlgorithm;
		mCandidates.add(c);
	}
	
	public void run(int cyclesPerFile) {

		logInfo("Resetting ...");
		mCandidates.forEach(c -> c.measuredNanoSeconds = 0);
		mMatrixStatistics.clear();
		
		logInfo("Searching files in \'" + mBenchmarkDirectory + "\' ...");
		List<Path> files = filesInBenchmark();
		logInfo("Found " + files.size() + " files.");

		logInfo("Starting benchmark (" + cyclesPerFile + " cycles per file).");

		long tStart, tLastProgressInfo;
		tStart = tLastProgressInfo = System.nanoTime();
		int filesRun = 0;
		for (Path file : files) {
			
			String fileContent = readFile(file);
			OctMatrix mOrig = null;
			try {
				if (fileContent != null) {
					mOrig = OctMatrix.parseBlockLowerTriangular(fileContent);
				}
			} catch (Exception e) {
				logWarning("Parsing matrix failed: " + file);
				logWarning(e.toString());
			}
			if (mOrig == null) {
				logWarning("Skipped file: " + file);
				continue;
			}
			if (mOrig.getSize() == 0) {
				logWarning("Skipped empty matrix: " + file);
				continue;
			}

			for (Candidate c : mCandidates) {
				OctMatrix[] mCopies = copyNTimes(mOrig, cyclesPerFile);
				long t = System.nanoTime();
				for (int i = 0; i < cyclesPerFile; ++i) {
					c.closureAlgorithm.accept(mCopies[i]);
				}
				c.measuredNanoSeconds += System.nanoTime() - t;
			}
			addStatistic(mOrig);
			++filesRun;

			if (System.nanoTime() > tLastProgressInfo + mProgressInfoIntervalInNanoSeconds) {
				tLastProgressInfo = System.nanoTime();
				double timeInSeconds = (System.nanoTime() - tStart) * 1e-9;
				logInfo(String.format("Running since %.1f seconds. Files run so far: %d", timeInSeconds, filesRun));
			}
		}
		double timeInSeconds = (System.nanoTime() - tStart) * 1e-9;
		logInfo(String.format("Finished benchmark after %.2f seconds.", timeInSeconds));
	}
	
	private void addStatistic(OctMatrix m) {
		MatrixStatistic ms = new MatrixStatistic();
		ms.variables = m.variables();
		ms.infinityPercentageInBlockLowerHalf = m.infinityPercentageInBlockLowerHalf();
		ms.isBottom = m.cachedStrongClosure().hasNegativeSelfLoop();
		ms.isBottomInt = m.cachedTightClosure().hasNegativeSelfLoop();
		mMatrixStatistics.add(ms);
	}

	private List<Path> filesInBenchmark() {
		try {
			// does not follow symbolic links
			return Files.walk(mBenchmarkDirectory)
				.filter(Files::isRegularFile)
				.filter(path -> {
					if (Files.isReadable(path)) {
						return true;
					} else {
						logWarning("Ignore unreadable file: " + path);
						return false;
					}
				})
				.collect(Collectors.toList());
		} catch (IOException e) {
			logWarning("Error while reading benchmark directory: " + mBenchmarkDirectory);
			logWarning(e.toString());
			return null;
		}
	}
	
	private String readFile(Path file) {
		BufferedReader br;
		StringBuilder sb = new StringBuilder();
		try {
			br = Files.newBufferedReader(file);
			try {
				String ln;
				while ((ln = br.readLine()) != null) {
					sb.append(ln);
					sb.append('\n');
				}
			} finally {
				br.close();
			}
		} catch (IOException e) {
			logWarning("Error while reading file: " + file);
			logWarning(e.toString());
			return null;
		}
		return sb.toString();
	}

	private OctMatrix[] copyNTimes(OctMatrix orig, int n) {
		OctMatrix[] copies = new OctMatrix[n];
		for (int i = 0; i < n; ++i) {
			copies[i] = orig.copy();
		}
		return copies;
	}
	

	public void printResults() {
		System.out.println();
		System.out.println("Benchmark Results");
		System.out.println("-----------------");
		System.out.println();

		List<Candidate> sortedResults = mCandidates;
		sortedResults = new ArrayList<>(mCandidates);
		Collections.sort(sortedResults, new Comparator<Candidate>() {
			@Override
			public int compare(Candidate ca, Candidate cb) {
				return Long.compare(ca.measuredNanoSeconds, cb.measuredNanoSeconds);
			}
		});
		int nameWidth = longestCandidateName();
		String format = "%" + nameWidth + "s %8.2f seconds%n";
		sortedResults.forEach(c -> System.out.format(format, c.name, c.measuredNanoSeconds * 1e-9));
	}
	
	public void printFullStatistics() {
		System.out.println();
		System.out.println("Full Statistics");
		System.out.println("---------------");
		System.out.println();
		
		System.out.println("#variables\t" + "infPercentage\t" + "isBottom\t" + "isBottomInt");
		for (MatrixStatistic ms : mMatrixStatistics) {
			System.out.format("%d\t%f\t%b\t%b%n",
					ms.variables, ms.infinityPercentageInBlockLowerHalf, ms.isBottom, ms.isBottomInt);
		}
		System.out.println();
	}

	public void printShortStatistics(int bins) {
		System.out.println();
		System.out.println("Short Statistics");
		System.out.println("----------------");
		System.out.println();

		long bottoms = mMatrixStatistics.stream().filter(ms -> ms.isBottom).count();
		long bottomInts = mMatrixStatistics.stream().filter(ms -> ms.isBottomInt).count();
		System.out.format("Matrices                 %8d%n", mMatrixStatistics.size());
		System.out.format("bottom matrices          %8d%n", bottoms);
		System.out.format("integer bottom matrices  %8d%n", bottomInts);
		System.out.println();
		
		System.out.println("Histogram: infinity percentage in block lower matrices (" + bins + " bins)");
		System.out.println(">=percentage #matrices");
		int[] histInfPercentage = histInfPercentagePerMatrix(bins);
		for (int bin = 0; bin < histInfPercentage.length; ++bin) {
			System.out.format("%12.2f %9d%n", (bin * 100.0 / bins), histInfPercentage[bin]);
		}
		System.out.println();
		
		System.out.println("Histogram: variables per matrix");
		System.out.println("variables #matrices ");
		int[] histVars = histVariablesPerMatrix();
		for (int varsPerMatrix = 0; varsPerMatrix < histVars.length; ++varsPerMatrix) {
			System.out.format("%9d %9d%n", varsPerMatrix, histVars[varsPerMatrix]);
		}
		System.out.println();
	}

	// map (size in #variables --> #matrices)
	public int[] histVariablesPerMatrix() {
		if (mMatrixStatistics.size() == 0) {
			return new int[0];
		}
		int[] sizes = mMatrixStatistics.stream().mapToInt(ms -> ms.variables).toArray();
		Arrays.sort(sizes);
		int maxSize = sizes[sizes.length - 1];
		int[] mapSizeToAbsFreq = new int[maxSize + 1];
		for (int s : sizes) {
			++mapSizeToAbsFreq[s];
		}
		return mapSizeToAbsFreq;
	}

	// map (infPercentage --> #matrices)
	public int[] histInfPercentagePerMatrix(int bins) {
		if (mMatrixStatistics.size() == 0) {
			return new int[0];
		}
		double[] infPercentages = mMatrixStatistics.stream()
				.mapToDouble(ms -> ms.infinityPercentageInBlockLowerHalf).toArray();
		Arrays.sort(infPercentages);
		int[] mapInfPercentageToAbsFreq = new int[bins + 1]; // last bin contains only matrices with 100% inf percentage
		for (double ip : infPercentages) {
			int bin = (int) (ip * bins);
			++mapInfPercentageToAbsFreq[bin];
		}
		return mapInfPercentageToAbsFreq;
	}
	
	private int longestCandidateName() {
		int max = 0;
		for (Candidate c : mCandidates) {
			max = Math.max(c.name.length(), max);
		}
		return max;
	}
	
	private void logInfo(String msg) {
		System.out.println(msg);
	}

	private void logWarning(String msg) {
		System.err.println(msg);
	}
}
