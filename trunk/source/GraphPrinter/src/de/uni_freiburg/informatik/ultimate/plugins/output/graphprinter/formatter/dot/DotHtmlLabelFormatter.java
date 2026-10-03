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
 * {@link LabelFormatter} for {@link AnnotationMode#HTML_LABELS}.
 *
 * <p>
 * Embeds metadata as DOT HTML-like labels on nodes and edges, using nested HTML tables with section headers, group
 * headers, and key-value leaf entries.
 * </p>
 *
 * @author Manuel Bentele
 */
public final class DotHtmlLabelFormatter implements LabelFormatter {

	@Override
	public String formatNodeLabel(final String label, final NodeInfo info) {
		if (info == null || !info.isGroup()) {
			return DotFormatter.escapeDotString(label);
		}

		return buildHtmlLabel(label, info, false);
	}

	@Override
	public String formatEdgeLabel(final String label, final NodeInfo info) {
		if (info == null || !info.isGroup()) {
			if (label == null || label.isEmpty()) {
				return null;
			}
			return DotFormatter.escapeDotString(label);
		}

		return buildHtmlLabel(label, info, true);
	}

	private static String buildHtmlLabel(final String label, final NodeInfo info, final boolean bordered) {
		final String innerBorder = bordered ? "1" : "0";
		final StringBuilder sb = new StringBuilder();

		sb.append("<");
		sb.append("<table border=\"0\" cellborder=\"0\" cellspacing=\"0\">");
		sb.append("<tr><td align=\"left\"><b>").append(escapeHtml(label)).append("</b></td></tr>");
		sb.append("<tr><td>");
		sb.append("<table border=\"").append(innerBorder).append("\" cellborder=\"0\" cellspacing=\"0\">");
		for (final NodeInfo section : info.getChildren()) {
			sb.append("<tr><td align=\"left\" colspan=\"2\"><b>").append(escapeHtml(section.getName()))
					.append("</b></td></tr>");

			renderHtmlChildren(sb, section.getChildren(), 1);
		}
		sb.append("</table>");
		sb.append("</td></tr>");
		sb.append("</table>>");

		return sb.toString();
	}

	private static void renderHtmlChildren(final StringBuilder sb, final List<NodeInfo> children, final int depth) {
		for (final NodeInfo child : children) {
			if (child.isLeaf()) {
				sb.append("<tr>");
				sb.append("<td align=\"left\">").append(escapeHtml(child.getName())).append("</td>");
				sb.append("<td align=\"left\">").append(escapeHtml(child.getValue())).append("</td>");
				sb.append("</tr>");
			} else {
				final String indent = "&nbsp;".repeat(Math.max(0, depth) * 2);

				sb.append("<tr>");
				sb.append("<td align=\"left\" colspan=\"2\"><i>").append(indent).append(escapeHtml(child.getName()))
						.append("</i></td>");
				sb.append("</tr>");

				renderHtmlChildren(sb, child.getChildren(), depth + 1);
			}
		}
	}

	private static String escapeHtml(final String input) {
		if (input == null) {
			return "";
		}

		return input.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace("\n", "<br/>")
				.replace("\r", "");
	}
}
