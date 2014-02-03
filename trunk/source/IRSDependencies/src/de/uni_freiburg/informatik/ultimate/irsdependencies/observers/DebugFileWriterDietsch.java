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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;

public class DebugFileWriterDietsch {

	private static Logger sLogger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);
	private List<List<RCFGEdge>> mPaths;
	private final int mUnrollingDepth;
	private final static String sFolderPath = "F:\\repos\\ultimate fresher co\\trunk\\examples\\unrolling-tests\\";

	public DebugFileWriterDietsch(List<List<RCFGEdge>> list, int unrollingDepth) {
		if (list == null) {
			throw new IllegalArgumentException("Parameter may not be null");
		}
		mUnrollingDepth = unrollingDepth;
		mPaths = list;
	}

	public void run() {
		if (mPaths.size() > 0) {
			HashMap<RootEdge, ArrayList<ArrayList<CodeBlock>>> tmp = new HashMap<>();

			for (List<RCFGEdge> path : mPaths) {
				if (path.size() > 0) {
					RCFGEdge first = path.get(0);
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

			StringBuilder sb;

			if (mPaths.size() > 1) {
				sb = createDebugOutput(tmp);
			} else {
				sb = new StringBuilder();
				for (ArrayList<ArrayList<CodeBlock>> e : tmp.values()) {
					for (ArrayList<CodeBlock> trace : e) {
						for (CodeBlock entry : trace) {
							sb.append(entry.getPrettyPrintedStatements());
							sb.append(" ");
						}
					}
				}
			}

			sb.append("\nNumber of traces in mPaths: ").append(mPaths.size());

			ProgramPoint r = (ProgramPoint) tmp.keySet().iterator().next()
					.getTarget();
			String currentFileName = Paths
					.get(r.getPayload().getLocation().getFileName())
					.getFileName().toString();
			String currentMethodName = (r).getProcedure();
			String filename = "dd_trace_" + currentFileName + "_"
					+ currentMethodName + "_dfs_n_" + mUnrollingDepth + ".txt";

			try {
				writeLargerTextFile(sFolderPath + filename, sb);
			} catch (IOException e) {
				sLogger.fatal(e.getStackTrace());
			}
		} else {
			sLogger.debug("No traces found; this may be due to infinite recursion");
		}
	}

	private StringBuilder createDebugOutput(
			HashMap<RootEdge, ArrayList<ArrayList<CodeBlock>>> procToTraces) {

		sLogger.debug("Creating debug output...");

		// find prefix & max trace length
		int prefixPos = -1;
		int maxTraceLength = -1;
		for (Entry<RootEdge, ArrayList<ArrayList<CodeBlock>>> en : procToTraces
				.entrySet())
			outerLoopPrefix: {
				for (int i = 0;; ++i) {
					CodeBlock acc = en.getValue().get(0).get(i);

					for (ArrayList<CodeBlock> trace : en.getValue()) {
						if (trace.size() > maxTraceLength) {
							maxTraceLength = trace.size();
						}
						if (i < trace.size()) {
							CodeBlock current = trace.get(i);
							if (acc != current) {
								prefixPos = i;
								break outerLoopPrefix;
							}
						} else {
							break outerLoopPrefix;
						}
					}
				}
			}

		// find suffix
		int suffixOffset = -1;
		for (Entry<RootEdge, ArrayList<ArrayList<CodeBlock>>> en : procToTraces
				.entrySet())
			outerLoopSuffix: {
				for (int i = 1;; ++i) {
					CodeBlock acc = en.getValue().get(0)
							.get(en.getValue().get(0).size() - i);
					int j = -1;
					for (ArrayList<CodeBlock> trace : en.getValue()) {
						j = trace.size() - i;
						if (j > 0) {
							CodeBlock current = trace.get(j);
							if (acc != current) {
								suffixOffset = i;
								break outerLoopSuffix;
							}
						} else {
							break outerLoopSuffix;
						}
					}
				}
			}

		// if suffix is only 1, dont use suffixes
		if (suffixOffset <= 1) {
			suffixOffset = 0;
		}

		// if prefix is only 1, dont use prefixes
		if (prefixPos <= 1) {
			prefixPos = 0;
		}

		// build renaming table for middle part
		HashMap<RCFGEdge, Integer> renaming = new HashMap<>();
		int maxSymbols = 0;
		for (Entry<RootEdge, ArrayList<ArrayList<CodeBlock>>> en : procToTraces
				.entrySet()) {
			for (int i = prefixPos; i < maxTraceLength; ++i) {
				for (ArrayList<CodeBlock> trace : en.getValue()) {
					if (i < trace.size() - suffixOffset + 1) {
						CodeBlock current = trace.get(i);
						if (!renaming.containsKey(current)) {
							maxSymbols++;
							renaming.put(current, maxSymbols);
						}
					}
				}
			}
		}

		TreeSet<String> set = new TreeSet<>();
		StringBuilder sb = new StringBuilder();
		StringBuilder rtr = new StringBuilder();

		// build and sort mapping table
		if (prefixPos > 1) {
			sb.append(getLetter(0));
			sb.append(" := Prefix of length ");
			sb.append(prefixPos);
			sb.append(" is ");
			outerloop: for (Entry<RootEdge, ArrayList<ArrayList<CodeBlock>>> en : procToTraces
					.entrySet()) {
				for (ArrayList<CodeBlock> trace : en.getValue()) {
					for (int i = 0; i < prefixPos; ++i) {
						CodeBlock c = trace.get(i);
						sb.append(c.getPrettyPrintedStatements());
						sb.append(" ");
					}
					break outerloop;
				}
			}
			set.add(sb.toString());
			sb = new StringBuilder();
		}
		for (Entry<RCFGEdge, Integer> entry : renaming.entrySet()) {
			sb.append(getLetter(entry.getValue()));
			sb.append(" := ");
			sb.append(((CodeBlock) entry.getKey()).getPrettyPrintedStatements());
			set.add(sb.toString());
			sb = new StringBuilder();
		}
		if (suffixOffset > 1) {
			sb.append(getLetter(maxSymbols + 1));
			sb.append(" := Suffix of length ");
			sb.append(suffixOffset - 1);
			sb.append(" is ");
			outerloop: for (Entry<RootEdge, ArrayList<ArrayList<CodeBlock>>> en : procToTraces
					.entrySet()) {
				for (ArrayList<CodeBlock> trace : en.getValue()) {
					for (int i = trace.size() - suffixOffset + 1; i < trace
							.size(); ++i) {
						CodeBlock c = trace.get(i);
						sb.append(c.getPrettyPrintedStatements());
						sb.append(" ");
					}
					break outerloop;
				}
			}
			set.add(sb.toString());
			sb = new StringBuilder();
		}
		for (String s : set) {
			rtr.append(s).append("\n");
		}
		rtr.append("\n");
		set.clear();

		// build and sort encoded traces for final output
		for (Entry<RootEdge, ArrayList<ArrayList<CodeBlock>>> en : procToTraces
				.entrySet()) {
			for (ArrayList<CodeBlock> trace : en.getValue()) {
				if (prefixPos > 1) {
					sb.append(getLetter(0));
					sb.append(",");
				}
				for (int i = prefixPos; i < trace.size() - suffixOffset + 1; ++i) {
					sb.append(getLetter(renaming.get(trace.get(i))));
					sb.append(",");
				}
				if (suffixOffset > 1) {
					sb.append(getLetter(maxSymbols + 1));
				} else {
					sb.replace(sb.length() - 1, sb.length(), "");
				}
				set.add(sb.toString());
				sb = new StringBuilder();
			}
		}

		for (String s : set) {
			rtr.append(s).append("\n");
		}

		return rtr;
	}

	private String getLetter(int i) {
		String rtr = "";

		while (i > 26) {
			rtr = rtr + "A";
			i = i - 26;
		}

		return rtr + "ABCDEFGHIJKLMNOPQRSTUVWXYZ".charAt(i);
	}

	private void writeLargerTextFile(String aFileName, StringBuilder sb)
			throws IOException {
		Path path = Paths.get(aFileName);
		sLogger.debug("Writing " + path.toString());
		BufferedWriter writer = Files.newBufferedWriter(path,
				StandardCharsets.UTF_8);
		writer.write(sb.toString());
		writer.close();
	}
}
