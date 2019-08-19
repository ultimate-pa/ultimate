/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 *
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.observers;

import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;

public class DebugFileWriterDietsch {

	private final ILogger mLogger;
	private final List<List<IcfgEdge>> mPaths;
	private final int mUnrollingDepth;
	private static final String FOLDER_PATH = "F:\\repos\\ultimate fresher co\\trunk\\examples\\unrolling-tests\\";

	public DebugFileWriterDietsch(final List<List<IcfgEdge>> list, final ILogger logger, final int unrollingDepth) {
		mLogger = logger;
		if (list == null) {
			throw new IllegalArgumentException("Parameter may not be null");
		}
		mUnrollingDepth = unrollingDepth;
		mPaths = list;
	}

	public void run() {
		if (mPaths.isEmpty()) {
			mLogger.debug("No traces found; this may be due to infinite recursion");
			return;
		}

		final Map<RootEdge, List<List<CodeBlock>>> tmp = new HashMap<>();

		for (final List<IcfgEdge> path : mPaths) {
			if (path.isEmpty()) {
				continue;
			}
			final IcfgEdge first = path.get(0);
			if (first instanceof RootEdge) {
				final RootEdge r = (RootEdge) first;
				if (!tmp.containsKey(r)) {
					tmp.put(r, new ArrayList<>());
				}
				final List<CodeBlock> cb = new ArrayList<>();
				for (int i = 1; i < path.size(); ++i) {
					cb.add((CodeBlock) path.get(i));
				}
				tmp.get(r).add(cb);
			}
		}

		StringBuilder sb;

		if (mPaths.size() > 1) {
			sb = createDebugOutput(tmp);
		} else {
			sb = new StringBuilder();
			for (final List<List<CodeBlock>> e : tmp.values()) {
				for (final List<CodeBlock> trace : e) {
					for (final CodeBlock entry : trace) {
						sb.append(entry.getPrettyPrintedStatements());
						sb.append(" ");
					}
				}
			}
		}

		sb.append("\nNumber of traces in mPaths: ").append(mPaths.size());

		final BoogieIcfgLocation r = (BoogieIcfgLocation) tmp.keySet().iterator().next().getTarget();
		final String currentFileName = Paths.get(ILocation.getAnnotation(r).getFileName()).getFileName().toString();
		final String currentMethodName = r.getProcedure();
		final String filename =
				"dd_trace_" + currentFileName + "_" + currentMethodName + "_dfs_n_" + mUnrollingDepth + ".txt";

		try {
			writeLargerTextFile(FOLDER_PATH + filename, sb);
		} catch (final IOException e) {
			mLogger.fatal(e.getStackTrace());
		}
	}

	private StringBuilder createDebugOutput(final Map<RootEdge, List<List<CodeBlock>>> procToTraces) {

		mLogger.debug("Creating debug output...");

		// find prefix & max trace length
		int prefixPos = -1;
		int maxTraceLength = -1;
		for (final Entry<RootEdge, List<List<CodeBlock>>> en : procToTraces.entrySet()) {
			outerLoopPrefix: {
				for (int i = 0;; ++i) {
					final CodeBlock acc = en.getValue().get(0).get(i);

					for (final List<CodeBlock> trace : en.getValue()) {
						if (trace.size() > maxTraceLength) {
							maxTraceLength = trace.size();
						}
						if (i < trace.size()) {
							final CodeBlock current = trace.get(i);
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
		}

		// find suffix
		int suffixOffset = -1;
		for (final Entry<RootEdge, List<List<CodeBlock>>> en : procToTraces.entrySet()) {
			outerLoopSuffix: {
				for (int i = 1;; ++i) {
					final CodeBlock acc = en.getValue().get(0).get(en.getValue().get(0).size() - i);
					int j = -1;
					for (final List<CodeBlock> trace : en.getValue()) {
						j = trace.size() - i;
						if (j > 0) {
							final CodeBlock current = trace.get(j);
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
		final HashMap<IcfgEdge, Integer> renaming = new HashMap<>();
		int maxSymbols = 0;
		for (final Entry<RootEdge, List<List<CodeBlock>>> en : procToTraces.entrySet()) {
			for (int i = prefixPos; i < maxTraceLength; ++i) {
				for (final List<CodeBlock> trace : en.getValue()) {
					if (i < trace.size() - suffixOffset) {
						final CodeBlock current = trace.get(i);
						if (!renaming.containsKey(current)) {
							maxSymbols++;
							renaming.put(current, maxSymbols);
						}
					}
				}
			}
		}

		final TreeSet<String> set = new TreeSet<>();
		StringBuilder sb = new StringBuilder();
		final StringBuilder rtr = new StringBuilder();

		// build and sort mapping table
		if (prefixPos > 1) {
			sb.append(getLetter(0));
			sb.append(" := Prefix of length ");
			sb.append(prefixPos);
			sb.append(" is ");
			for (final Entry<RootEdge, List<List<CodeBlock>>> en : procToTraces.entrySet()) {
				if (en.getValue().isEmpty()) {
					continue;
				}
				final List<CodeBlock> trace = en.getValue().get(0);
				for (int i = 0; i < prefixPos; ++i) {
					final CodeBlock c = trace.get(i);
					sb.append(c.getPrettyPrintedStatements());
					sb.append(" ");
				}
				break;
			}
			set.add(sb.toString());
			sb = new StringBuilder();
		}
		for (final Entry<IcfgEdge, Integer> entry : renaming.entrySet()) {
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
			for (final Entry<RootEdge, List<List<CodeBlock>>> en : procToTraces.entrySet()) {
				if (en.getValue().isEmpty()) {
					continue;
				}
				final List<CodeBlock> trace = en.getValue().get(0);
				for (int i = trace.size() - suffixOffset + 1; i < trace.size(); ++i) {
					final CodeBlock c = trace.get(i);
					sb.append(c.getPrettyPrintedStatements());
					sb.append(" ");
				}
				break;
			}
			set.add(sb.toString());
			sb = new StringBuilder();
		}
		for (final String s : set) {
			rtr.append(s).append("\n");
		}
		rtr.append("\n");
		set.clear();

		// build and sort encoded traces for final output
		for (final Entry<RootEdge, List<List<CodeBlock>>> en : procToTraces.entrySet()) {
			for (final List<CodeBlock> trace : en.getValue()) {
				if (prefixPos > 1) {
					sb.append(getLetter(0));
					sb.append(",");
				}
				for (int i = prefixPos; i < trace.size() - suffixOffset; ++i) {
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

		for (final String s : set) {
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

	private void writeLargerTextFile(final String aFileName, final StringBuilder sb) throws IOException {
		final Path path = Paths.get(aFileName);
		mLogger.debug("Writing " + path.toString());
		final BufferedWriter writer = Files.newBufferedWriter(path, StandardCharsets.UTF_8);
		writer.write(sb.toString());
		writer.close();
	}
}
