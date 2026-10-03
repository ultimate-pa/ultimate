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

package de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter.dot;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter.LabelFormatter;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter.NodeInfo;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.preferences.GraphPrinterPreferenceValues.AnnotationMode;

/**
 * {@link LabelFormatter} for {@link AnnotationMode#RECORD_NODES}.
 *
 * <p>
 * Renders metadata as separate DOT record nodes connected to the parent node/edge via dashed edges. The primary node
 * keeps a plain label; the record node contains the flattened metadata tree.
 * </p>
 *
 * @author Manuel Bentele
 */
public final class DotRecordLabelFormatter implements LabelFormatter {

	@Override
	public String formatNodeLabel(final String label, final NodeInfo info) {
		return DotFormatter.escapeDotString(label);
	}

	@Override
	public String formatEdgeLabel(final String label, final NodeInfo info) {
		if (label == null || label.isEmpty()) {
			return null;
		}

		return DotFormatter.escapeDotString(label);
	}

	@Override
	public List<String> additionalNodeDeclarations(final String nodeId, final String label, final NodeInfo info) {
		if (info == null || !info.isGroup()) {
			return List.of();
		}

		final String recordId = nodeId + "_info";
		final String recordAttrs = DotFormatter.nodeAttributes(
				"{" + DotFormatter.escapeDotString(label) + " information|" + buildRecordFields(info) + "}", true,
				DotFormatter.RECORD_FILL_COLOR);
		final String recordNode = recordId + " [shape=record, " + recordAttrs + "];";
		final String recordEdge = nodeId + " -> " + recordId + " [style=dashed, color=gray, dir=none];";

		return List.of(recordNode, recordEdge);
	}

	@Override
	public List<String> additionalEdgeDeclarations(final String sourceId, final String targetId, final String label,
			final NodeInfo info) {
		if (info == null || !info.isGroup()) {
			return List.of();
		}

		final String recordId = sourceId + "_" + targetId + "_info";
		final String recordAttrs = DotFormatter.nodeAttributes("{Edge information|" + buildRecordFields(info) + "}",
				true, DotFormatter.RECORD_FILL_COLOR);
		final String recordNode = recordId + " [shape=record, " + recordAttrs + "];";
		final String recordEdge = sourceId + " -> " + recordId + " [style=dashed, color=gray, dir=none];";

		return List.of(recordNode, recordEdge);
	}

	private static String buildRecordFields(final NodeInfo info) {
		final StringBuilder sb = new StringBuilder();
		boolean first = true;

		for (final NodeInfo section : info.getChildren()) {
			if (!first) {
				sb.append("|");
			}

			first = false;

			sb.append("{").append(DotFormatter.escapeDotString(section.getName())).append("|{");
			flattenRecordFields(sb, section.getChildren());
			sb.append("}}");
		}

		return sb.toString();
	}

	private static void flattenRecordFields(final StringBuilder sb, final List<NodeInfo> children) {
		boolean first = true;

		for (final NodeInfo child : children) {
			if (child.isLeaf()) {
				if (!first) {
					sb.append("|");
				}

				first = false;

				sb.append(DotFormatter.escapeDotString(child.getName())).append(": ")
						.append(DotFormatter.escapeDotString(child.getValue()));
			} else {
				if (!first) {
					sb.append("|");
				}

				first = false;

				sb.append("{").append(DotFormatter.escapeDotString(child.getName())).append("|{");
				flattenRecordFields(sb, child.getChildren());
				sb.append("}}");
			}
		}
	}
}
