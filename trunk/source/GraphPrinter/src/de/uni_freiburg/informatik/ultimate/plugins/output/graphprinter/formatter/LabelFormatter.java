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

package de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter;

import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.preferences.GraphPrinterPreferenceValues.AnnotationMode;

/**
 * Strategy interface for formatting node and edge labels in DOT output.
 *
 * <p>
 * Each {@link AnnotationMode} has a corresponding {@link LabelFormatter} implementation that controls how labels and
 * metadata ({@link NodeInfo}) are rendered in the DOT file.
 * </p>
 *
 * @author Manuel Bentele
 */
public interface LabelFormatter {

	/**
	 * Formats a node label, optionally enriched with metadata.
	 *
	 * @param label
	 *            The primary label text.
	 * @param info
	 *            The metadata tree, or {@code null} if no metadata is available.
	 * @return The DOT attribute value for the node label (without surrounding brackets or {@code label=} prefix).
	 */
	String formatNodeLabel(String label, NodeInfo info);

	/**
	 * Formats an edge label, optionally enriched with metadata.
	 *
	 * @param label
	 *            The primary label text, or {@code null}/{@code ""} if the edge has no label.
	 * @param info
	 *            The metadata tree, or {@code null} if no metadata is available.
	 * @return The DOT attribute value for the edge label (without surrounding brackets or {@code label=} prefix), or
	 *         {@code null} if the edge should have no label attribute at all.
	 */
	String formatEdgeLabel(String label, NodeInfo info);

	/**
	 * Returns additional DOT node declarations (e.g. record nodes) that should be emitted alongside the main node.
	 *
	 * @param nodeId
	 *            The DOT identifier of the node.
	 * @param label
	 *            The primary label text.
	 * @param info
	 *            The metadata tree, or {@code null}.
	 * @return A list of additional DOT node declaration strings, or an empty list if none.
	 */
	default java.util.List<String> additionalNodeDeclarations(final String nodeId, final String label,
			final NodeInfo info) {
		return java.util.List.of();
	}

	/**
	 * Returns additional DOT edge declarations (e.g. edges to record nodes) that should be emitted alongside the main
	 * edge.
	 *
	 * @param sourceId
	 *            The DOT identifier of the source node.
	 * @param targetId
	 *            The DOT identifier of the target node.
	 * @param label
	 *            The primary label text.
	 * @param info
	 *            The metadata tree, or {@code null}.
	 * @return A list of additional DOT edge declaration strings, or an empty list if none.
	 */
	default java.util.List<String> additionalEdgeDeclarations(final String sourceId, final String targetId,
			final String label, final NodeInfo info) {
		return java.util.List.of();
	}
}
