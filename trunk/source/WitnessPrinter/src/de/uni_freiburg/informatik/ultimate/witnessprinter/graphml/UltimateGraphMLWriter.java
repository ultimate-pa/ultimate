package de.uni_freiburg.informatik.ultimate.witnessprinter.graphml;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Map.Entry;

import org.apache.commons.collections15.Transformer;

import edu.uci.ics.jung.graph.Hypergraph;
import edu.uci.ics.jung.graph.UndirectedGraph;
import edu.uci.ics.jung.io.GraphMLMetadata;
import edu.uci.ics.jung.io.GraphMLWriter;

/**
 * Extended Jung GraphMLWriter s.t. attr.name is also written (for yED) and XML boilerplate is changeable.
 * 
 * The code is copied from JUNG 2.0 via grepcode and modified at the appropriate places.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UltimateGraphMLWriter<V, E> extends GraphMLWriter<V, E> {

	private static final String XML_VERSION = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
	private static final String GRAPHML_OPEN = "<graphml " + "xmlns=\"http://graphml.graphdrawing.org/xmlns\" "
			+ "xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xsi:schemaLocation="
			+ "\"http://graphml.graphdrawing.org/xmlns http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd\">\n";

	@Override
	protected void writeKeySpecification(final String key, final String type, final GraphMLMetadata<?> ds,
			final BufferedWriter bw) throws IOException {
		bw.write("<key id=\"" + key + "\" attr.name=\"" + key + "\" for=\"" + type + "\"");
		boolean closed = false;
		// write out description if any
		final String desc = ds.description;
		if (desc != null) {
			bw.write(">\n");
			closed = true;
			bw.write("<desc>" + desc + "</desc>\n");
		}
		// write out default if any
		final Object def = ds.default_value;
		if (def != null) {
			if (!closed) {
				bw.write(">\n");
				closed = true;
			}
			bw.write("<default>" + def.toString() + "</default>\n");
		}
		if (!closed) {
			bw.write("/>\n");
		} else {
			bw.write("</key>\n");
		}
	}

	@Override
	public void save(final Hypergraph<V, E> graph, final Writer writer) throws IOException {
		final BufferedWriter bw = new BufferedWriter(writer);

		// write out boilerplate header
		bw.write(XML_VERSION);
		bw.write(GRAPHML_OPEN);

		// write out data specifiers, including defaults
		for (final Entry<String, GraphMLMetadata<Hypergraph<V, E>>> entry : graph_data.entrySet()) {
			writeKeySpecification(entry.getKey(), "graph", entry.getValue(), bw);
		}
		for (final Entry<String, GraphMLMetadata<V>> entry : vertex_data.entrySet()) {
			writeKeySpecification(entry.getKey(), "node", entry.getValue(), bw);
		}
		for (final Entry<String, GraphMLMetadata<E>> entry : edge_data.entrySet()) {
			writeKeySpecification(entry.getKey(), "edge", entry.getValue(), bw);
		}

		// write out graph-level information
		// set edge default direction
		bw.write("<graph edgedefault=\"");
		directed = !(graph instanceof UndirectedGraph);
		if (directed) {
			bw.write("directed\">\n");
		} else {
			bw.write("undirected\">\n");
		}

		// write graph description, if any
		final String desc = graph_desc.transform(graph);
		if (desc != null) {
			bw.write("<desc>" + desc + "</desc>\n");
		}

		// write graph data out if any
		for (final Entry<String, GraphMLMetadata<Hypergraph<V, E>>> entry : graph_data.entrySet()) {
			final Transformer<Hypergraph<V, E>, ?> t = entry.getValue().transformer;
			final Object value = t.transform(graph);
			if (value != null) {
				bw.write(format("data", "key", entry.getKey(), value.toString()) + "\n");
			}
		}

		// write vertex information
		writeVertexData(graph, bw);

		// write edge information
		writeEdgeData(graph, bw);

		// close graph
		bw.write("</graph>\n");
		bw.write("</graphml>\n");
		bw.flush();

		bw.close();
	}

}
