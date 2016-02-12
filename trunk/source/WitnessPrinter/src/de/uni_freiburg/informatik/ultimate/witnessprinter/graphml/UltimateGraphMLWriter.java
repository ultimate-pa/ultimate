package de.uni_freiburg.informatik.ultimate.witnessprinter.graphml;

import java.io.BufferedWriter;
import java.io.IOException;

import edu.uci.ics.jung.io.GraphMLMetadata;
import edu.uci.ics.jung.io.GraphMLWriter;

/**
 * Extended Jung GraphMLWriter s.t. attr.name is also written (for yED).
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <V>
 * @param <E>
 */
public class UltimateGraphMLWriter<V, E> extends GraphMLWriter<V, E> {

	@Override
	protected void writeKeySpecification(String key, String type, GraphMLMetadata<?> ds, BufferedWriter bw)
			throws IOException {
		bw.write("<key id=\"" + key + "\" attr.name=\"" + key + "\" for=\"" + type + "\"");
		boolean closed = false;
		// write out description if any
		String desc = ds.description;
		if (desc != null) {
			if (!closed) {
				bw.write(">\n");
				closed = true;
			}
			bw.write("<desc>" + desc + "</desc>\n");
		}
		// write out default if any
		Object def = ds.default_value;
		if (def != null) {
			if (!closed) {
				bw.write(">\n");
				closed = true;
			}
			bw.write("<default>" + def.toString() + "</default>\n");
		}
		if (!closed)
			bw.write("/>\n");
		else
			bw.write("</key>\n");
	}
}
