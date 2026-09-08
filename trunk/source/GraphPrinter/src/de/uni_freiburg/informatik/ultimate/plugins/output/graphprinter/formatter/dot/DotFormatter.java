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

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter.IGraphFormatter;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter.LabelFormatter;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter.NodeInfo;
import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.preferences.GraphPrinterPreferenceValues.AnnotationMode;

/**
 * A standalone {@link IGraphFormatter} implementation that produces DOT (Graphviz) format output.
 *
 * <p>
 * Supports three annotation output modes via {@link AnnotationMode}, each backed by a dedicated {@link LabelFormatter}:
 * </p>
 * <ul>
 * <li>{@link AnnotationMode#NONE}: no annotations in the output ({@link DotPlainLabelFormatter})</li>
 * <li>{@link AnnotationMode#HTML_LABELS}: annotations are embedded as HTML labels ({@link DotHtmlLabelFormatter})</li>
 * <li>{@link AnnotationMode#RECORD_NODES}: annotations are rendered as separate record nodes
 * ({@link DotRecordLabelFormatter})</li>
 * </ul>
 *
 * <p>
 * All plain-text labels are escaped for DOT compatibility: backslashes, double quotes, newlines, and carriage returns
 * are escaped. HTML labels use DOT HTML-like string formatting and are not escaped the same way.
 * </p>
 *
 * @author Manuel Bentele
 */
public class DotFormatter implements IGraphFormatter {

	private static final String NODE_FILL_COLOR = "#E8F0FE";
	static final String RECORD_FILL_COLOR = "#F0F0F0";

	private String mGraphName;
	private final List<String> mNodeDeclarations;
	private final List<String> mEdgeDeclarations;
	private LabelFormatter mLabelFormatter;

	public DotFormatter() {
		this(AnnotationMode.NONE);
	}

	public DotFormatter(final AnnotationMode annotationMode) {
		mGraphName = "graph";
		mNodeDeclarations = new ArrayList<>();
		mEdgeDeclarations = new ArrayList<>();
		setAnnotationMode(Objects.requireNonNull(annotationMode));
	}

	/**
	 * Sets the annotation output mode and selects the corresponding {@link LabelFormatter}.
	 *
	 * @param annotationMode
	 *            The mode, must not be {@code null}.
	 */
	public void setAnnotationMode(final AnnotationMode annotationMode) {
		mLabelFormatter = switch (Objects.requireNonNull(annotationMode)) {
		case NONE -> new DotPlainLabelFormatter();
		case HTML_LABELS -> new DotHtmlLabelFormatter();
		case RECORD_NODES -> new DotRecordLabelFormatter();
		};
	}

	@Override
	public void setGraphName(final String name) {
		mGraphName = Objects.requireNonNullElse(name, "graph");
	}

	@Override
	public void addNode(final String id, final String label) {
		addNode(id, label, null);
	}

	@Override
	public void addNode(final String id, final String label, final NodeInfo info) {
		final String formattedLabel = mLabelFormatter.formatNodeLabel(label, info);
		final boolean isHtml = mLabelFormatter instanceof DotHtmlLabelFormatter && info != null && info.isGroup();
		mNodeDeclarations.add(id + " [" + nodeAttributes(formattedLabel, !isHtml, NODE_FILL_COLOR) + "];");
		mNodeDeclarations.addAll(mLabelFormatter.additionalNodeDeclarations(id, label, info));
	}

	@Override
	public void addEdge(final String sourceId, final String targetId, final String label) {
		addEdge(sourceId, targetId, label, (NodeInfo) null);
	}

	@Override
	public void addEdge(final String sourceId, final String targetId, final String label, final NodeInfo info) {
		final String formattedLabel = mLabelFormatter.formatEdgeLabel(label, info);
		if (formattedLabel == null) {
			mEdgeDeclarations.add(sourceId + " -> " + targetId + ";");
		} else {
			final boolean isHtml = mLabelFormatter instanceof DotHtmlLabelFormatter && info != null && info.isGroup();
			mEdgeDeclarations.add(sourceId + " -> " + targetId + " [" + labelAttribute(formattedLabel, !isHtml) + "];");
		}

		mEdgeDeclarations.addAll(mLabelFormatter.additionalEdgeDeclarations(sourceId, targetId, label, info));
	}

	@Override
	public String getFileEnding() {
		return ".dot";
	}

	@Override
	public String getString() {
		final StringBuilder sb = new StringBuilder();

		sb.append("digraph \"").append(escapeDotString(mGraphName)).append("\" {\n");
		sb.append("    node [shape=box];\n");
		for (final String nodeDecl : mNodeDeclarations) {
			sb.append("    ").append(nodeDecl).append("\n");
		}
		for (final String edgeDecl : mEdgeDeclarations) {
			sb.append("    ").append(edgeDecl).append("\n");
		}
		sb.append("}\n");

		return sb.toString();
	}

	@Override
	public void writeFile(final Path path) throws IOException {
		Files.createDirectories(path.getParent());
		Files.write(path, getString().getBytes(StandardCharsets.UTF_8));
	}

	/**
	 * Builds a DOT label attribute string.
	 *
	 * @param label
	 *            The formatted label text.
	 * @param quote
	 *            Whether to wrap the label in double quotes. Use {@code false} for HTML labels.
	 * @return The DOT attribute string.
	 */
	static String labelAttribute(final String label, final boolean quote) {
		return quote ? "label=\"" + label + "\"" : "label=" + label;
	}

	/**
	 * Builds DOT node attributes with label, fill style, and fill color.
	 *
	 * @param label
	 *            The formatted label text.
	 * @param quote
	 *            Whether to wrap the label in double quotes. Use {@code false} for HTML labels.
	 * @param fillColor
	 *            The fill color (e.g. {@code #E8F0FE}).
	 * @return The DOT attribute string.
	 */
	static String nodeAttributes(final String label, final boolean quote, final String fillColor) {
		return labelAttribute(label, quote) + ", style=filled, fillcolor=\"" + fillColor + "\"";
	}

	/**
	 * Escapes a string for safe use inside DOT double-quoted labels.
	 *
	 * @param input
	 *            The raw string to escape.
	 * @return The escaped string, or an empty string if {@code input} is {@code null}.
	 */
	static String escapeDotString(final String input) {
		if (input == null) {
			return "";
		}

		return input.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n").replace("\r", "\\r");
	}
}
