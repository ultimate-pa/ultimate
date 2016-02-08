package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
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
		ClosureBenchmark cb = new ClosureBenchmark("/tmp/closureBenchmark", 10);
		cb.addCandidate("naiv", OctMatrix::shortestPathClosureNaiv);
		cb.addCandidate("apron", OctMatrix::shortestPathClosureApron);
		cb.addCandidate("fsparse", OctMatrix::shortestPathClosureFullSparse);
		cb.addCandidate("sparse", OctMatrix::shortestPathClosureSparse);
		cb.addCandidate("psparse", OctMatrix::shortestPathClosurePrimitiveSparse);
		cb.run();
		cb.printResults(false);
		cb.printResults(true);
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
	
	////////////////////////////////////////////////////////////////
	
	
	private final Path mBenchmarkDirectory;
	private final List<Candidate> mCandidates;
	private final int mCyclesPerFile;
	private final long mProgressInfoIntervalInNanoSeconds = 10_000_000_000L; // 10 seconds
	
	public ClosureBenchmark(String benchmarkDirectory, int cyclesPerFile) {
		mBenchmarkDirectory = Paths.get(benchmarkDirectory);
		mCandidates = new ArrayList<>();
		mCyclesPerFile = cyclesPerFile;
	}
	
	public void addCandidate(String name, Consumer<OctMatrix> closureAlgorithm) {
		Candidate c = new Candidate();
		c.name = name;
		c.closureAlgorithm = closureAlgorithm;
		mCandidates.add(c);
	}
	
	public void run() {
		
		List<Path> files = filesInBenchmark();
		logInfo("Found " + files.size() + " files.");
		logInfo("Starting benchmark.");

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

			for (Candidate c : mCandidates) {
				OctMatrix[] mCopies = copyNTimes(mOrig, mCyclesPerFile);
				long t = System.nanoTime();
				for (int i = 0; i < mCyclesPerFile; ++i) {
					c.closureAlgorithm.accept(mCopies[i]);
				}
				c.measuredNanoSeconds += System.nanoTime() - t;
			}
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
	

	public void printResults(boolean sort) {
		System.out.println();
		System.out.println("Benchmark results");
		System.out.println("-----------------");
		System.out.println();

		List<Candidate> sortedResults = mCandidates;
		if (sort) {
			sortedResults = new ArrayList<>(mCandidates);
			Collections.sort(sortedResults, new Comparator<Candidate>() {
				@Override
				public int compare(Candidate ca, Candidate cb) {
					return Long.compare(ca.measuredNanoSeconds, cb.measuredNanoSeconds);
				}
			});
		}
		int nameWidth = longestCandidateName();
		String format = "%" + nameWidth + "s %8.2f seconds%n";
		sortedResults.forEach(c -> System.out.format(format, c.name, c.measuredNanoSeconds * 1e-9));
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
