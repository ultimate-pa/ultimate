package de.uni_freiburg.informatik.ultimate.irsdependencies.observers;

import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;
import java.util.TreeSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.irsdependencies.Activator;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;

public class DebugFileWriterNutz {

	private static Logger sLogger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);
	private List<List<RCFGEdge>> mPaths;
	private final int mUnrollingDepth;
	private final static String sFolderPath = "F:\\repos\\ultimate fresher co\\trunk\\examples\\unrolling-tests\\";

	public DebugFileWriterNutz(List<List<RCFGEdge>> paths, int unrollingDepth) {
		if (paths == null) {
			throw new IllegalArgumentException("Parameter may not be null");
		}
		mUnrollingDepth = unrollingDepth;
		mPaths = paths;
	}

	public void run() {
		HashMap<RootEdge, ArrayList<ArrayList<CodeBlock>>> tmp = new HashMap<>();

		for (List<RCFGEdge> path : mPaths) {
			if (path.size() > 0) {
				IWalkable first = path.get(0);
				if (first instanceof RootEdge) {
					RootEdge r = (RootEdge) first;
					if (!tmp.containsKey(r)) {
						tmp.put(r, new ArrayList<ArrayList<CodeBlock>>());
					}
					ArrayList<CodeBlock> cb = new ArrayList<>();
					for (int i = 1; i < path.size(); ++i) {
						cb.add((CodeBlock) path.get(i));
					}
					tmp.get(r).add(cb);
				}
			}
		}

		prepareTraces(mUnrollingDepth, tmp);
	}

	private void prepareTraces(int unrollingDepth,
			HashMap<RootEdge, ArrayList<ArrayList<CodeBlock>>> procToTraces) {
		sLogger.debug("Sorting all traces of each procedure...");
		HashMap<RootEdge, TreeSet<String>> procToTraceStrings = new HashMap<RootEdge, TreeSet<String>>();
		for (Entry<RootEdge, ArrayList<ArrayList<CodeBlock>>> en : procToTraces
				.entrySet()) {
			TreeSet<String> allProcTraces = new TreeSet<String>();
			for (ArrayList<CodeBlock> trace : en.getValue()) {
				String traceString = traceToString(trace);
				allProcTraces.add("--------\n" + traceString);
			}
			procToTraceStrings.put(en.getKey(), allProcTraces);
		}
		sLogger.debug("Writing all traces of Main to file...");
		try {
			for (Entry<RootEdge, TreeSet<String>> en : procToTraceStrings
					.entrySet()) {
				String currentFileName = Paths
						.get(((ProgramPoint) en.getKey().getTarget())
								.getPayload().getLocation().getFileName())
						.getFileName().toString();
				String currentMethodName = ((ProgramPoint) en.getKey()
						.getTarget()).getProcedure();
				String filename = "dd_rcfgTraces_" + currentFileName + "_"
						+ currentMethodName + "__dfs_" + "_n_is_"
						+ unrollingDepth + "_" + ".txt";

				writeLargerTextFile(sFolderPath + filename, en.getValue());
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private String traceToString(ArrayList<CodeBlock> trace) {
		StringBuilder sb = new StringBuilder();
		for (CodeBlock cb : trace) {
			sb.append(cb.getPrettyPrintedStatements());
			sb.append("\n");
		}
		return sb.toString();
	}

	private void writeLargerTextFile(String aFileName, TreeSet<String> traces)
			throws IOException {
		Path path = Paths.get(aFileName);
		sLogger.debug("Writing " + path.toString());
		try (BufferedWriter writer = Files.newBufferedWriter(path,
				StandardCharsets.UTF_8)) {
			for (String line : traces) {
				writer.write(line);
				writer.newLine();
			}
		}
	}
}
