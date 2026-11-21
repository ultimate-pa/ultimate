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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.lib.icfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter.NodeInfo;

/**
 * Extracts metadata from {@link VisualizationNode}s and {@link VisualizationEdge}s into a tree of {@link NodeInfo}s.
 *
 * <p>
 * The extracted tree contains all payload annotations from {@link IPayload#getAnnotations()}, with each
 * {@link IAnnotations} expanded into its {@code toString()} representation. Special rendering is applied to known types
 * such as {@link ILocation} (showing line and column numbers).
 * </p>
 *
 * @author Manuel Bentele
 */
public final class NodeInfoExtractor {

	private NodeInfoExtractor() {
	}

	/**
	 * Extracts metadata from a {@link VisualizationNode}.
	 *
	 * @param node
	 *            The visualization node.
	 * @return An {@link NodeInfo} tree, or {@code null} if no metadata is available.
	 */
	public static NodeInfo extractNodeInfo(final VisualizationNode node) {
		if (node == null) {
			return null;
		}

		final List<NodeInfo> sections = new ArrayList<>();

		if (node.hasPayload()) {
			final NodeInfo annotationSection = createAnnotationSection(node.getPayload());
			if (annotationSection != null) {
				sections.add(annotationSection);
			}
		}

		return new NodeInfo("info", sections);
	}

	/**
	 * Extracts metadata from a {@link VisualizationEdge}.
	 *
	 * @param edge
	 *            The visualization edge.
	 * @return An {@link NodeInfo} tree, or {@code null} if no metadata is available.
	 */
	public static NodeInfo extractEdgeInfo(final VisualizationEdge edge) {
		if (edge == null) {
			return null;
		}

		final List<NodeInfo> sections = new ArrayList<>();

		if (edge.hasPayload()) {
			final NodeInfo annotationSection = createAnnotationSection(edge.getPayload());
			if (annotationSection != null) {
				sections.add(annotationSection);
			}
		}

		return new NodeInfo("info", sections);
	}

	private static NodeInfo createAnnotationSection(final IPayload payload) {
		if (payload == null || !payload.hasAnnotation()) {
			return null;
		}

		final List<NodeInfo> children = new ArrayList<>();
		for (final Map.Entry<String, IAnnotations> entry : payload.getAnnotations().entrySet()) {
			final IAnnotations annotation = entry.getValue();
			if (annotation == null) {
				continue;
			}

			if (annotation instanceof BoogieIcfgContainer) {
				continue;
			}

			children.add(convertValue(getShortClassName(entry.getKey()), annotation));
		}

		return children.isEmpty() ? null : new NodeInfo("Annotations", children);
	}

	private static String getShortClassName(final String name) {
		final String[] parts = name.split("\\.");

		if (parts.length - 1 > 0) {
			return parts[parts.length - 1];
		}

		return new String();
	}

	private static NodeInfo convertValue(final String name, final Object value) {
		if (value == null) {
			return new NodeInfo(name, "null");
		}

		if (value instanceof final ILocation loc) {
			return convertLocation(name, loc);
		}

		return new NodeInfo(name, String.valueOf(value));
	}

	private static NodeInfo convertLocation(final String name, final ILocation loc) {
		return new NodeInfo(name, String.format("L%d:%d – L%d:%d", loc.getStartLine(), loc.getStartColumn(),
				loc.getEndLine(), loc.getEndColumn()));
	}

}
