package de.uni_freiburg.informatik.ultimate.witnessprinter;

import java.util.function.Function;

import org.apache.commons.collections15.Transformer;

import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.GeneratedWitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.GeneratedWitnessNode;
import edu.uci.ics.jung.graph.Hypergraph;
import edu.uci.ics.jung.io.GraphMLWriter;

public abstract class BaseWitnessGenerator<TE, E> {
	
	public abstract String makeGraphMLString();

	protected void addGraphData(final GraphMLWriter<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graphWriter, final String key, final String defaultValue, final Function<Hypergraph<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>>, String> transformer) {
		assert transformer != null;
		graphWriter.addGraphData(key, null, defaultValue,
				new Transformer<Hypergraph<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>>, String>() {
					@Override
					public String transform(final Hypergraph<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> arg0) {
						return transformer.apply(arg0);
					}
				});
	}

	protected void addEdgeData(final GraphMLWriter<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graphWriter, final String key, final String defaultValue, final Function<GeneratedWitnessEdge<TE, E>, String> transformer) {
		assert transformer != null;
		graphWriter.addEdgeData(key, null, defaultValue, new Transformer<GeneratedWitnessEdge<TE, E>, String>() {
			@Override
			public String transform(final GeneratedWitnessEdge<TE, E> arg0) {
				return transformer.apply(arg0);
			}
		});
	}

	protected void addVertexData(final GraphMLWriter<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graphWriter, final String key, final String defaultValue, final Function<GeneratedWitnessNode, String> transformer) {
		assert transformer != null;
		graphWriter.addVertexData(key, null, defaultValue, new Transformer<GeneratedWitnessNode, String>() {
			@Override
			public String transform(final GeneratedWitnessNode arg0) {
				return transformer.apply(arg0);
			}
		});
	}
}