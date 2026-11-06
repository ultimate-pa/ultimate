/*
 * Copyright (C) 2026 Manuel Bentele
 *
 * This file is part of the ULTIMATE GraphPrinter plug-in.
 *
 * The ULTIMATE GraphPrinter plug-in is free software: you can redistribute it and/or modify it under the terms of the
 * GNU Lesser General Public License as published by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE GraphPrinter plug-in is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the ULTIMATE GraphPrinter
 * plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE GraphPrinter plug-in, or any
 * covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the ULTIMATE GraphPrinter plug-in grant you
 * additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IVisualizable;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter.IGraphFormatter;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter.dot.DotFormatter;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.preferences.GraphPrinterPreferenceValues;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.preferences.GraphPrinterPreferenceValues.AnnotationMode;

/**
 * Observer that traverses {@link VisualizationNode} graphs and writes them to files using an {@link IGraphFormatter}.
 *
 * The observer checks if the root {@link IElement} is {@link IVisualizable}, obtains the {@link VisualizationNode} via
 * {@link IVisualizable#getVisualizationGraph()}, and performs a traversal to collect all nodes and edges. The resulting
 * graph is written to a file using an {@link IGraphFormatter} formatter.
 *
 * @author Manuel Bentele
 */
public class GraphPrinterObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final ModelType mInputGraphType;
	private final IUltimateServiceProvider mServices;

	private IGraphFormatter mFormatter;
	private final Map<VisualizationNode, String> mNodeIds;
	private final Set<VisualizationNode> mVisitedNodes;
	private final Map<VisualizationEdge, Boolean> mSeenEdges;
	private int mNodeCounter;

	public GraphPrinterObserver(final ILogger logger, final ModelType graphType,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mInputGraphType = graphType;
		mServices = services;

		mNodeIds = new HashMap<>();
		mVisitedNodes = new LinkedHashSet<>();
		mSeenEdges = new HashMap<>();
		mNodeCounter = 0;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(GraphPrinter.PLUGIN_ID);
		final AnnotationMode annotationMode =
				prefs.getEnum(GraphPrinterPreferenceValues.LABEL_GRAPH_ANNOTATION_MODE, AnnotationMode.class);

		mFormatter = new DotFormatter(annotationMode);
		mFormatter.setGraphName(getGraphName(modelType));

		mNodeIds.clear();
		mVisitedNodes.clear();
		mSeenEdges.clear();
		mNodeCounter = 0;
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof final IVisualizable visu) {
			final IVisualizable<?> visualizationGraph = visu.getVisualizationGraph();
			if (visualizationGraph instanceof final VisualizationNode rootNode) {
				dfstraverse(rootNode);
				return false;
			}
		}

		mLogger.error("Model is not visualizable: " + root);
		return false;
	}

	@Override
	public void finish() {
		if (mFormatter == null || mVisitedNodes.isEmpty()) {
			return;
		}

		writeFile();
	}

	private void writeFile() {
		final Path outputPath = constructOutputPath();
		try {
			mLogger.info("Write graph to " + outputPath);
			mFormatter.writeFile(outputPath);
		} catch (final IOException e) {
			mLogger.error("Could not write graph file: " + outputPath, e);
		}
	}

	private Path constructOutputPath() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(GraphPrinter.PLUGIN_ID);
		final String directory = prefs.getString(GraphPrinterPreferenceValues.LABEL_GRAPH_DIRECTORY);
		final String filename = prefs.getString(GraphPrinterPreferenceValues.LABEL_GRAPH_FILENAME);
		final boolean besidesInputFile = prefs.getBoolean(GraphPrinterPreferenceValues.LABEL_GRAPH_BESIDES_INPUT_FILE);

		String basePath;
		if (besidesInputFile && mInputGraphType != null && mInputGraphType.getNumberOfFiles() > 0) {
			basePath = mInputGraphType.getAbsolutePath(0);
		} else {
			basePath = directory + File.separator + filename;
		}

		final String suffix = getModelTypeSuffix(mInputGraphType);
		return Path.of(basePath + "_" + suffix + mFormatter.getFileEnding());
	}

	private void dfstraverse(final VisualizationNode node) {
		final String nodeId = getOrCreateNodeId(node);
		mFormatter.addNode(nodeId, getNodeLabel(node), NodeInfoExtractor.extractNodeInfo(node));
		mVisitedNodes.add(node);

		final List<VisualizationNode> children = node.getOutgoingNodes();
		if (children != null) {
			for (final VisualizationNode child : children) {
				final String childId = getOrCreateNodeId(child);
				for (final VisualizationEdge edge : node.getOutgoingEdges()) {
					if (edge.getTarget().equals(child) && !mSeenEdges.containsKey(edge)) {
						mFormatter.addEdge(nodeId, childId, getEdgeLabel(edge), NodeInfoExtractor.extractEdgeInfo(edge));
						mSeenEdges.put(edge, true);
					}
				}
			}

			for (final VisualizationNode child : children) {
				if (!mVisitedNodes.contains(child)) {
					dfstraverse(child);
				}
			}
		}
	}

	private String getOrCreateNodeId(final VisualizationNode node) {
		return mNodeIds.computeIfAbsent(node, k -> "node" + Integer.toString(mNodeCounter++));
	}

	private static String getNodeLabel(final VisualizationNode node) {
		final Object backing = node.getBacking();
		if (backing != null) {
			return improveLabel(backing.toString(), backing);
		}

		return improveLabel(node.toString(), node);
	}

	/**
	 * Returns a meaningful label for a {@link VisualizationEdge}.
	 *
	 * Uses the edge's {@code toString()} (which delegates to the backing object). If the result looks like a default
	 * {@link Object#toString()} (i.e., {@code ClassName@hexhash}), the simple class name of the backing is used
	 * instead.
	 *
	 * @param edge
	 *            The visualization edge.
	 * @return A human-readable label for the edge.
	 */
	private static String getEdgeLabel(final VisualizationEdge edge) {
		final String rawLabel = edge.toString();
		final Object backing = edge.getBacking();
		return improveLabel(rawLabel, backing);
	}

	/**
	 * Improves a label by checking if it looks like a default {@link Object#toString()} output (pattern
	 * {@code ClassName@hexhash}). If so, the simple class name of the backing object is used instead.
	 *
	 * @param rawLabel
	 *            The original label string.
	 * @param backing
	 *            The backing object, used to determine the simple class name. May be {@code null}.
	 * @return An improved label, or the original if it does not look like a default toString.
	 */
	private static String improveLabel(final String rawLabel, final Object backing) {
		if (rawLabel == null || rawLabel.isEmpty()) {
			return backing != null ? backing.getClass().getSimpleName() : "";
		}

		// Check for default Object.toString() pattern: ClassName@hexhash
		if (rawLabel.matches("^[^@]+@[0-9a-fA-F]+$")) {
			return backing != null ? backing.getClass().getSimpleName() : rawLabel;
		}

		return rawLabel;
	}

	private static String getGraphName(final ModelType graphType) {
		if (graphType == null) {
			return "graph";
		}

		final StringBuilder sb = new StringBuilder();
		final String[] parts = graphType.getCreator().split("\\.");

		if (parts.length - 1 > 0) {
			sb.append(parts[parts.length - 1]);
		} else {
			sb.append(graphType.getCreator());
		}

		return sb.toString();
	}

	private static String getModelTypeSuffix(final ModelType graphType) {
		if (graphType == null || graphType.getType() == null) {
			return "graph";
		}

		return graphType.getType().name();
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

}
