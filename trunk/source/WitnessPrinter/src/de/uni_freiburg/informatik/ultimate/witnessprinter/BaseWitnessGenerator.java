package de.uni_freiburg.informatik.ultimate.witnessprinter;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.GeneratedWitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.GeneratedWitnessNode;
import de.uni_freiburg.informatik.ultimate.witnessprinter.preferences.PreferenceInitializer;
import edu.uci.ics.jung.graph.Hypergraph;
import edu.uci.ics.jung.io.GraphMLWriter;

public abstract class BaseWitnessGenerator<TE, E> {
	
	private final IUltimateServiceProvider mServices;
	
	public BaseWitnessGenerator(final IUltimateServiceProvider services) {
		mServices = services;
	}
	
	public abstract String makeGraphMLString();
	
	protected void addCanonicalWitnessGraphData(
			final GraphMLWriter<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graphWriter,
			final String witnessType) {
		addGraphData(graphWriter, "sourcecodelang", null, graph -> "C");
		addGraphData(graphWriter, "witness-type", null, graph -> witnessType);
		
		final IPreferenceProvider ups = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		
		writePassthroughWitnessGraphData(graphWriter, ups, "producer", PreferenceInitializer.LABEL_GRAPH_DATA_PRODUCER);
		writePassthroughWitnessGraphData(graphWriter, ups, "specification",
				PreferenceInitializer.LABEL_GRAPH_DATA_SPECIFICATION);
		writePassthroughWitnessGraphData(graphWriter, ups, "programhash",
				PreferenceInitializer.LABEL_GRAPH_DATA_PROGRAMHASH);
		writePassthroughWitnessGraphData(graphWriter, ups, "architecture",
				PreferenceInitializer.LABEL_GRAPH_DATA_ARCHITECTURE);
		
		final String timestamp = CoreUtil.getIsoUtcTimestamp();
		addGraphData(graphWriter, "creationtime", null, graph -> timestamp);
	}
	
	private void writePassthroughWitnessGraphData(
			final GraphMLWriter<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graphWriter,
			final IPreferenceProvider ups, final String graphDataAttribute, final String preferenceLabel) {
		final String value = ups.getString(preferenceLabel);
		if (value == null || PreferenceInitializer.UNUSED_GRAPH_DATA.equals(value)) {
			return;
		}
		addGraphData(graphWriter, graphDataAttribute, null, graph -> value);
	}
	
	protected void addGraphData(final GraphMLWriter<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graphWriter,
			final String key, final String defaultValue,
			final Function<Hypergraph<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>>, String> transformer) {
		assert transformer != null;
		graphWriter.addGraphData(key, null, defaultValue, transformer::apply);
	}
	
	protected void addEdgeData(final GraphMLWriter<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graphWriter,
			final String key, final String defaultValue,
			final Function<GeneratedWitnessEdge<TE, E>, String> transformer) {
		assert transformer != null;
		graphWriter.addEdgeData(key, null, defaultValue, transformer::apply);
	}
	
	protected void addVertexData(final GraphMLWriter<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graphWriter,
			final String key, final String defaultValue, final Function<GeneratedWitnessNode, String> transformer) {
		assert transformer != null;
		graphWriter.addVertexData(key, null, defaultValue, transformer::apply);
	}
}