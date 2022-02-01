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
import java.util.Map.Entry;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;

public class DebugFileWriterNutz {

	private final ILogger mLogger;
	private final List<List<IcfgEdge>> mPaths;
	private final int mUnrollingDepth;
	private final static String sFolderPath = "F:\\repos\\ultimate fresher co\\trunk\\examples\\unrolling-tests\\";

	public DebugFileWriterNutz(final List<List<IcfgEdge>> paths, final ILogger logger, final int unrollingDepth) {
		mLogger = logger;
		if (paths == null) {
			throw new IllegalArgumentException("Parameter may not be null");
		}
		mUnrollingDepth = unrollingDepth;
		mPaths = paths;
	}

	public void run() {
		final HashMap<RootEdge, ArrayList<ArrayList<CodeBlock>>> tmp = new HashMap<>();

		for (final List<IcfgEdge> path : mPaths) {
			if (!path.isEmpty()) {
				final IWalkable first = path.get(0);
				if (first instanceof RootEdge) {
					final RootEdge r = (RootEdge) first;
					if (!tmp.containsKey(r)) {
						tmp.put(r, new ArrayList<ArrayList<CodeBlock>>());
					}
					final ArrayList<CodeBlock> cb = new ArrayList<>();
					for (int i = 1; i < path.size(); ++i) {
						cb.add((CodeBlock) path.get(i));
					}
					tmp.get(r).add(cb);
				}
			}
		}

		prepareTraces(mUnrollingDepth, tmp);
	}

	private void prepareTraces(final int unrollingDepth,
			final HashMap<RootEdge, ArrayList<ArrayList<CodeBlock>>> procToTraces) {
		mLogger.debug("Sorting all traces of each procedure...");
		final HashMap<RootEdge, TreeSet<String>> procToTraceStrings = new HashMap<>();
		for (final Entry<RootEdge, ArrayList<ArrayList<CodeBlock>>> en : procToTraces.entrySet()) {
			final TreeSet<String> allProcTraces = new TreeSet<>();
			for (final ArrayList<CodeBlock> trace : en.getValue()) {
				final String traceString = traceToString(trace);
				allProcTraces.add("--------\n" + traceString);
			}
			procToTraceStrings.put(en.getKey(), allProcTraces);
		}
		mLogger.debug("Writing all traces of Main to file...");
		try {
			for (final Entry<RootEdge, TreeSet<String>> en : procToTraceStrings.entrySet()) {
				final String currentFileName = Paths.get(ILocation.getAnnotation(en.getKey().getTarget()).getFileName())
						.getFileName().toString();
				final String currentMethodName = ((BoogieIcfgLocation) en.getKey().getTarget()).getProcedure();
				final String filename = "dd_rcfgTraces_" + currentFileName + "_" + currentMethodName + "__dfs_"
						+ "_n_is_" + unrollingDepth + "_" + ".txt";

				writeLargerTextFile(sFolderPath + filename, en.getValue());
			}
		} catch (final IOException e) {
			e.printStackTrace();
		}
	}

	private String traceToString(final ArrayList<CodeBlock> trace) {
		final StringBuilder sb = new StringBuilder();
		for (final CodeBlock cb : trace) {
			sb.append(cb.getPrettyPrintedStatements());
			sb.append("\n");
		}
		return sb.toString();
	}

	private void writeLargerTextFile(final String aFileName, final TreeSet<String> traces) throws IOException {
		final Path path = Paths.get(aFileName);
		mLogger.debug("Writing " + path.toString());
		try (BufferedWriter writer = Files.newBufferedWriter(path, StandardCharsets.UTF_8)) {
			for (final String line : traces) {
				writer.write(line);
				writer.newLine();
			}
		}
	}
}
