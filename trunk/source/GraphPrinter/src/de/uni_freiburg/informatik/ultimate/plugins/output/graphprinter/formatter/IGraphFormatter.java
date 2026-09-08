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

import java.io.IOException;
import java.nio.file.Path;

import de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter.dot.DotFormatter;

/**
 * Interface for graph formatters that can build a graph representation from nodes and edges and write it to a file.
 *
 * Implementations include {@link DotFormatter} for the DOT (Graphviz) format. Other implementations could support
 * GraphML, JSON, or other graph serialization formats.
 *
 * @author Manuel Bentele
 */
public interface IGraphFormatter {

	/**
	 * Sets the name of the graph.
	 *
	 * @param name
	 *            The graph name.
	 */
	void setGraphName(String name);

	/**
	 * Adds a node to the graph representation.
	 *
	 * @param id
	 *            The unique identifier of the node.
	 * @param label
	 *            The human-readable label of the node.
	 */
	void addNode(String id, String label);

	/**
	 * Adds a node with metadata to the graph representation.
	 *
	 * @param id
	 *            The unique identifier of the node.
	 * @param label
	 *            The human-readable label of the node.
	 * @param info
	 *            A tree of metadata extracted from the node, or {@code null} if no metadata is available.
	 */
	void addNode(String id, String label, NodeInfo info);

	/**
	 * Adds a directed edge to the graph representation.
	 *
	 * @param sourceId
	 *            The identifier of the source node.
	 * @param targetId
	 *            The identifier of the target node.
	 * @param label
	 *            The human-readable label of the edge, or {@code null} if the edge has no label.
	 */
	void addEdge(String sourceId, String targetId, String label);

	/**
	 * Adds a directed edge with metadata to the graph representation.
	 *
	 * @param sourceId
	 *            The identifier of the source node.
	 * @param targetId
	 *            The identifier of the target node.
	 * @param label
	 *            The human-readable label of the edge, or {@code null} if the edge has no label.
	 * @param info
	 *            A tree of metadata extracted from the edge, or {@code null} if no metadata is available.
	 */
	void addEdge(String sourceId, String targetId, String label, NodeInfo info);

	/**
	 * Returns the file ending (including the leading dot) used by this formatter for output files.
	 *
	 * @return The file ending, e.g. {@code ".dot"}.
	 */
	String getFileEnding();

	/**
	 * Returns the string representation of the graph in the formatter's format.
	 *
	 * @return The formatted graph string.
	 */
	String getString();

	/**
	 * Writes the graph representation to a file at the given path.
	 *
	 * @param path
	 *            The path where the file should be written.
	 * @throws IOException
	 *             If writing the file fails.
	 */
	void writeFile(Path path) throws IOException;

}
