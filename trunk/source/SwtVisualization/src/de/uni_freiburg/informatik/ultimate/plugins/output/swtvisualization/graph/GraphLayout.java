/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE SwtVisualization plug-in.
 *
 * The ULTIMATE SwtVisualization plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SwtVisualization plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SwtVisualization plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SwtVisualization plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SwtVisualization plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.graph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.widgets.Display;

import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;

/**
 * Computes layout positions for graph nodes using a tree-based BFS algorithm.
 * <p>
 * Nodes are arranged in layers (y-coordinates) based on BFS depth from the root. Within each layer, nodes are
 * distributed horizontally. Back-edges (edges to already-visited nodes) are detected and stored separately.
 */
public class GraphLayout {

	private static final int HORIZONTAL_SPACING = 40;
	private static final int VERTICAL_SPACING = 80;
	private static final int NODE_PADDING = 16;
	private static final int NODE_HEIGHT = 28;
	private static final int MIN_NODE_WIDTH = 40;

	private final Map<VisualizationNode, NodeLayoutInfo> mNodePositions;
	private final Set<VisualizationEdge> mBackEdges;
	private final List<VisualizationNode> mNodes;
	private final List<VisualizationEdge> mEdges;
	private final VisualizationNode mRootNode;
	private double mGraphWidth;
	private double mGraphHeight;

	public GraphLayout(final VisualizationNode rootNode, final List<VisualizationNode> nodes,
			final List<VisualizationEdge> edges) {
		mRootNode = rootNode;
		mNodes = nodes;
		mEdges = edges;
		mNodePositions = new LinkedHashMap<>();
		mBackEdges = new HashSet<>();
	}

	/**
	 * Compute the layout using a BFS tree layout.
	 *
	 * @param gc
	 *            A {@link GC} used for measuring text extent. May be {@code null}; in that case a temporary GC is
	 *            created.
	 */
	public void computeLayout(final GC gc) {
		mNodePositions.clear();
		mBackEdges.clear();

		GC measureGc = gc;
		boolean createdTempGc = false;
		if (measureGc == null || measureGc.isDisposed()) {
			measureGc = new GC(Display.getDefault());
			createdTempGc = true;
		}

		try {
			// Build adjacency from edges
			final Map<VisualizationNode, List<VisualizationNode>> childrenMap = new HashMap<>();
			final Map<VisualizationNode, List<VisualizationEdge>> edgeMap = new HashMap<>();
			final Set<VisualizationNode> visited = new HashSet<>();

			for (final VisualizationNode node : mNodes) {
				childrenMap.put(node, new ArrayList<>());
				edgeMap.put(node, new ArrayList<>());
			}

			for (final VisualizationEdge edge : mEdges) {
				final VisualizationNode source = edge.getSource();
				final VisualizationNode target = edge.getTarget();
				if (source != null && target != null && childrenMap.containsKey(source)) {
					childrenMap.get(source).add(target);
					edgeMap.get(source).add(edge);
				}
			}

			// BFS layering
			final List<List<VisualizationNode>> layers = new ArrayList<>();
			final Set<VisualizationNode> placed = new HashSet<>();

			final List<VisualizationNode> currentLayer = new ArrayList<>();
			currentLayer.add(mRootNode);
			placed.add(mRootNode);
			layers.add(currentLayer);

			while (!currentLayer.isEmpty()) {
				final List<VisualizationNode> nextLayer = new ArrayList<>();
				for (final VisualizationNode node : currentLayer) {
					final List<VisualizationNode> children = childrenMap.get(node);
					if (children == null) {
						continue;
					}
					for (final VisualizationNode child : children) {
						if (!placed.contains(child)) {
							placed.add(child);
							nextLayer.add(child);
						} else {
							// This edge is a back-edge (or cross-edge)
							for (final VisualizationEdge edge : edgeMap.get(node)) {
								if (edge.getTarget().equals(child)) {
									mBackEdges.add(edge);
								}
							}
						}
					}
				}
				if (!nextLayer.isEmpty()) {
					layers.add(nextLayer);
				}
				currentLayer.clear();
				currentLayer.addAll(nextLayer);
			}

			// Mark remaining edges to already-placed nodes as back-edges
			for (final VisualizationEdge edge : mEdges) {
				if (mBackEdges.contains(edge)) {
					continue;
				}
				final VisualizationNode source = edge.getSource();
				final VisualizationNode target = edge.getTarget();
				if (source == null || target == null) {
					continue;
				}
				// If target was placed before source (in an earlier layer), it's a back-edge
				final int sourceLayer = findLayer(layers, source);
				final int targetLayer = findLayer(layers, target);
				if (targetLayer >= 0 && sourceLayer >= 0 && targetLayer <= sourceLayer) {
					mBackEdges.add(edge);
				}
			}

			// Position nodes within layers
			double yOffset = VERTICAL_SPACING;
			double maxWidth = 0;

			for (final List<VisualizationNode> layer : layers) {
				final int nodeCount = layer.size();
				// Compute total width needed for this layer
				int totalWidth = 0;
				final int[] widths = new int[nodeCount];
				for (int i = 0; i < nodeCount; i++) {
					final String label = getLabel(layer.get(i));
					final org.eclipse.swt.graphics.Point extent = measureGc.stringExtent(label);
					widths[i] = Math.max(MIN_NODE_WIDTH, extent.x + NODE_PADDING);
					totalWidth += widths[i];
				}
				totalWidth += HORIZONTAL_SPACING * (nodeCount - 1);
				maxWidth = Math.max(maxWidth, totalWidth);

				double xOffset = HORIZONTAL_SPACING;
				for (int i = 0; i < nodeCount; i++) {
					final VisualizationNode node = layer.get(i);
					mNodePositions.put(node, new NodeLayoutInfo(xOffset + widths[i] / 2.0, yOffset, widths[i],
							NODE_HEIGHT));
					xOffset += widths[i] + HORIZONTAL_SPACING;
				}
				yOffset += NODE_HEIGHT + VERTICAL_SPACING;
			}

			mGraphWidth = maxWidth + 2 * HORIZONTAL_SPACING;
			mGraphHeight = yOffset;
		} finally {
			if (createdTempGc) {
				measureGc.dispose();
			}
		}
	}

	private static int findLayer(final List<List<VisualizationNode>> layers, final VisualizationNode node) {
		for (int i = 0; i < layers.size(); i++) {
			if (layers.get(i).contains(node)) {
				return i;
			}
		}
		return -1;
	}

	private static String getLabel(final VisualizationNode node) {
		final String s = node.toString();
		return s.length() > 30 ? s.substring(0, 30) : s;
	}

	public Map<VisualizationNode, NodeLayoutInfo> getNodePositions() {
		return mNodePositions;
	}

	public Set<VisualizationEdge> getBackEdges() {
		return mBackEdges;
	}

	public double getGraphWidth() {
		return mGraphWidth;
	}

	public double getGraphHeight() {
		return mGraphHeight;
	}

	/**
	 * Get the layout to use, based on the preference string.
	 *
	 * @param layoutName
	 *            The layout name from preferences.
	 * @return Always returns a GraphLayout; the name is currently only for future extensibility.
	 */
	public static GraphLayout create(final String layoutName, final VisualizationNode rootNode,
			final List<VisualizationNode> nodes, final List<VisualizationEdge> edges) {
		// Currently only TreeLayout is supported; LayeredLayout would extend this
		return new GraphLayout(rootNode, nodes, edges);
	}
}
