package de.uni_freiburg.informatik.ultimate.witnessparser;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import org.apache.commons.collections15.Transformer;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessLocation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNodeAnnotation;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.uci.ics.jung.io.GraphIOException;
import edu.uci.ics.jung.io.graphml.EdgeMetadata;
import edu.uci.ics.jung.io.graphml.GraphMLReader2;
import edu.uci.ics.jung.io.graphml.GraphMetadata;
import edu.uci.ics.jung.io.graphml.HyperEdgeMetadata;
import edu.uci.ics.jung.io.graphml.NodeMetadata;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class WitnessAutomatonConstructor {

	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;
	private HashMap<String, WitnessNode> mNodes;

	public WitnessAutomatonConstructor(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	public IElement constructWitnessAutomaton(File file) {
		DirectedSparseGraph<WitnessNode, WitnessEdge> graph = getGraph(file);
		// find starting element(s)
		HashSet<WitnessNode> initialNodes = new HashSet<>();
		for (WitnessNode v : graph.getVertices()) {
			if (v.getIncomingEdges().size() == 0) {
				initialNodes.add(v);
			}
		}

		if (initialNodes.size() != 1) {
			throw new IllegalArgumentException("This file contains a witness with more than one initial state");
		}

		WitnessNode initial = initialNodes.iterator().next();

		printDebug(initial);

		return initial;
	}

	private void printDebug(WitnessNode initial) {
		if (!mLogger.isDebugEnabled()) {
			return;
		}
		// print the current graph
		ArrayDeque<WitnessNode> nodes = new ArrayDeque<>();
		HashSet<WitnessNode> closed = new HashSet<>();
		int edgeCount = 0;

		mLogger.debug(initial);
		for (WitnessEdge e : initial.getOutgoingEdges()) {
			mLogger.debug("\t-- " + e + "--> " + e.getTarget());
			nodes.add(e.getTarget());
			++edgeCount;
		}

		while (!nodes.isEmpty()) {
			WitnessNode current = nodes.removeFirst();
			if (closed.contains(current)) {
				continue;
			}
			closed.add(current);
			mLogger.debug(current);
			for (WitnessEdge e : current.getOutgoingEdges()) {
				mLogger.debug("\t-- " + e + "--> " + e.getTarget());
				nodes.addFirst(e.getTarget());
				++edgeCount;
			}
		}

		mLogger.debug("Graph has " + closed.size() + 1 + " nodes and " + edgeCount + " edges");
	}

	private DirectedSparseGraph<WitnessNode, WitnessEdge> getGraph(File file) {

		try {
			mNodes = new HashMap<>();

			Transformer<GraphMetadata, DirectedSparseGraph<WitnessNode, WitnessEdge>> graphTransformer = new Transformer<GraphMetadata, DirectedSparseGraph<WitnessNode, WitnessEdge>>() {
				@Override
				public DirectedSparseGraph<WitnessNode, WitnessEdge> transform(GraphMetadata arg0) {

					DirectedSparseGraph<WitnessNode, WitnessEdge> graph = new DirectedSparseGraph<WitnessNode, WitnessEdge>();
					for (Entry<Object, NodeMetadata> e : arg0.getNodeMap().entrySet()) {
						graph.addVertex((WitnessNode) e.getKey());
					}
					for (Entry<Object, EdgeMetadata> e : arg0.getEdgeMap().entrySet()) {
						WitnessEdge edge = (WitnessEdge) e.getKey();
						graph.addEdge(edge, edge.getSource(), edge.getTarget());
					}
					return graph;
				}
			};
			Transformer<NodeMetadata, WitnessNode> vertexTransformer = new Transformer<NodeMetadata, WitnessNode>() {
				@Override
				public WitnessNode transform(NodeMetadata data) {
					WitnessNode node = createNode(data.getId());
					WitnessNodeAnnotation annot = new WitnessNodeAnnotation(false, false);

					String entry = data.getProperties().get("entry");
					if (entry != null && Boolean.valueOf(entry)) {
						annot.setIsInitial(true);
						annot.annotate(node);
					}
					String error = data.getProperties().get("violation");
					if (error != null && Boolean.valueOf(error)) {
						annot.setIsError(true);
						annot.annotate(node);
					}

					return node;
				}
			};
			Transformer<EdgeMetadata, WitnessEdge> edgeTransformer = new Transformer<EdgeMetadata, WitnessEdge>() {
				@Override
				public WitnessEdge transform(EdgeMetadata data) {

					WitnessNode source = createNode(data.getSource());
					WitnessNode target = createNode(data.getTarget());

					String linestr = data.getProperties().get("originline");

					// set line to line if there is a valid line, -1 otherwise
					int line = 0;
					if (linestr != null) {
						try {
							line = Integer.valueOf(linestr);
						} catch (Exception ex) {
							line = -1;
						}
					} else {
						line = -1;
					}
					String orgfile = data.getProperties().get("originfile");
					String sourcecode = data.getProperties().get("sourcecode");

					WitnessLocation loc = new WitnessLocation(orgfile, line);
					WitnessEdge edge = new WitnessEdge(source, target, data.getId(), loc, sourcecode);

					WitnessEdgeAnnotation annot = new WitnessEdgeAnnotation(data.getProperties().get("negated"), data
							.getProperties().get("enterFunction"), data.getProperties().get("returnFrom"), data
							.getProperties().get("tokens"), data.getProperties().get("assumption"));
					if (!annot.isEmpty()) {
						annot.annotate(edge);
					}
					return edge;
				}
			};
			Transformer<HyperEdgeMetadata, WitnessEdge> hyperEdgeTransformer = new Transformer<HyperEdgeMetadata, WitnessEdge>() {
				@Override
				public WitnessEdge transform(HyperEdgeMetadata arg0) {
					// there shouldnt be any hyper edges
					return null;
				}
			};
			GraphMLReader2<DirectedSparseGraph<WitnessNode, WitnessEdge>, WitnessNode, WitnessEdge> reader2 = new GraphMLReader2<DirectedSparseGraph<WitnessNode, WitnessEdge>, WitnessNode, WitnessEdge>(
					new FileReader(file), graphTransformer, vertexTransformer, edgeTransformer, hyperEdgeTransformer);
			reader2.init();
			return reader2.readGraph();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (GraphIOException e) {
			e.printStackTrace();
		}
		return null;
	}

	private WitnessNode createNode(String id) {
		WitnessNode node = mNodes.get(id);
		if (node == null) {
			node = new WitnessNode(id);
			mNodes.put(node.getName(), node);
		}
		return node;
	}

}
