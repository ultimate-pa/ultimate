/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE WitnessParser plug-in.
 *
 * The ULTIMATE WitnessParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE WitnessParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.witnessparser;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import org.apache.commons.collections15.Transformer;

import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType.Type;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessGraphAnnotation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessGraphAnnotation.WitnessType;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessLocation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNodeAnnotation;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.uci.ics.jung.io.GraphIOException;
import edu.uci.ics.jung.io.graphml.AbstractMetadata;
import edu.uci.ics.jung.io.graphml.EdgeMetadata;
import edu.uci.ics.jung.io.graphml.GraphMLReader2;
import edu.uci.ics.jung.io.graphml.GraphMetadata;
import edu.uci.ics.jung.io.graphml.HyperEdgeMetadata;
import edu.uci.ics.jung.io.graphml.NodeMetadata;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class WitnessAutomatonConstructor {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private Map<String, WitnessNode> mNodes;
	private ModelType.Type mWitnessType;
	private WitnessGraphAnnotation mGraphAnnotation;

	public WitnessAutomatonConstructor(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	public IElement constructWitnessAutomaton(final File file) {
		final DirectedSparseGraph<WitnessNode, WitnessEdge> graph = getGraph(file);
		if (graph == null) {
			final String message = "Witness file is invalid";
			final IResult res = new GenericResult(Activator.PLUGIN_ID, message, message, Severity.ERROR);
			mLogger.error(res);
			mServices.getResultService().reportResult(Activator.PLUGIN_ID, res);
			mServices.getProgressMonitorService().cancelToolchain();
			return null;
		}
		// find starting element(s)
		final Set<WitnessNode> initialNodes =
				graph.getVertices().stream().filter(a -> a.getIncomingEdges().size() == 0).collect(Collectors.toSet());

		if (initialNodes.size() > 1) {
			throw new IllegalArgumentException("This file contains a witness with more than one initial location");
		} else if (initialNodes.isEmpty()) {
			throw new IllegalArgumentException("This file contains a witness without an initial location");
		}

		final WitnessNode initial = initialNodes.iterator().next();
		validate(initial);

		printDebug(initial);

		mGraphAnnotation.annotate(initial);
		switch (mGraphAnnotation.getWitnessType()) {
		case VIOLATION_WITNESS:
			mWitnessType = Type.VIOLATION_WITNESS;
			break;
		case CORRECTNESS_WITNESS:
			mWitnessType = Type.CORRECTNESS_WITNESS;
			break;
		default:
			mWitnessType = Type.OTHER;
			break;
		}

		return initial;
	}

	private void validate(final WitnessNode initial) {
		//@formatter:off
		//TODO: Check if witness conforms to "the rules" and if not, throw an exception:
		//- TRUE witness darf keine Assumption haben
		//- TRUE witness darf keinen Node mit Violation haben
		//- FALSE witness muss mindestens einen Node mit Violation haben
		//- FALSE witness darf keine Invarianten haben
		//@formatter:on
	}

	private void printDebug(final WitnessNode initial) {
		if (!mLogger.isDebugEnabled()) {
			return;
		}
		// print the current graph
		final Deque<WitnessNode> nodes = new ArrayDeque<>();
		final Set<WitnessNode> closed = new HashSet<>();
		int edgeCount = 0;

		mLogger.debug(initial);
		for (final WitnessEdge e : initial.getOutgoingEdges()) {
			mLogger.debug("\t-- " + e + "--> " + e.getTarget());
			nodes.add(e.getTarget());
			++edgeCount;
		}

		while (!nodes.isEmpty()) {
			final WitnessNode current = nodes.removeFirst();
			if (closed.contains(current)) {
				continue;
			}
			closed.add(current);
			mLogger.debug(current);
			for (final WitnessEdge e : current.getOutgoingEdges()) {
				mLogger.debug("\t-- " + e + "--> " + e.getTarget());
				nodes.addFirst(e.getTarget());
				++edgeCount;
			}
		}

		mLogger.debug("Graph has " + closed.size() + 1 + " nodes and " + edgeCount + " edges");
	}

	private DirectedSparseGraph<WitnessNode, WitnessEdge> getGraph(final File file) {

		try {
			mNodes = new HashMap<>();
			final GraphMLReader2<DirectedSparseGraph<WitnessNode, WitnessEdge>, WitnessNode, WitnessEdge> reader =
					getGraphMLReader(file);
			reader.init();
			return reader.readGraph();
		} catch (final FileNotFoundException e) {
			e.printStackTrace();
		} catch (final GraphIOException e) {
			e.printStackTrace();
		}
		return null;
	}

	private GraphMLReader2<DirectedSparseGraph<WitnessNode, WitnessEdge>, WitnessNode, WitnessEdge>
			getGraphMLReader(final File file) throws FileNotFoundException {
		final Transformer<GraphMetadata, DirectedSparseGraph<WitnessNode, WitnessEdge>> graphTransformer =
				getGraphTransformer();
		final Transformer<NodeMetadata, WitnessNode> vertexTransformer = getVertexTransformer();
		final Transformer<EdgeMetadata, WitnessEdge> edgeTransformer = getEdgeTransformer();
		final Transformer<HyperEdgeMetadata, WitnessEdge> hyperEdgeTransformer = getHyperEdgeTransformer();
		return new GraphMLReader2<DirectedSparseGraph<WitnessNode, WitnessEdge>, WitnessNode, WitnessEdge>(
				new FileReader(file), graphTransformer, vertexTransformer, edgeTransformer, hyperEdgeTransformer);
	}

	private Transformer<HyperEdgeMetadata, WitnessEdge> getHyperEdgeTransformer() {
		return new Transformer<HyperEdgeMetadata, WitnessEdge>() {
			@Override
			public WitnessEdge transform(final HyperEdgeMetadata arg0) {
				// there should not be any hyper edges
				return null;
			}
		};
	}

	private Transformer<EdgeMetadata, WitnessEdge> getEdgeTransformer() {
		return new Transformer<EdgeMetadata, WitnessEdge>() {
			@Override
			public WitnessEdge transform(final EdgeMetadata data) {

				final WitnessNode source = createNode(data.getSource());
				final WitnessNode target = createNode(data.getTarget());

				final int startline = getIntProperty(data, "startline");
				final int endline = getIntProperty(data, "endline");

				// TODO: Calculate column from offsets
				// final int startoffset = getIntProperty(data, "startoffset");
				// final int endoffset = getIntProperty(data, "endoffset");

				final String orgfile = data.getProperties().get("originfile");
				final String sourcecode = data.getProperties().get("sourcecode");

				final WitnessLocation loc = new WitnessLocation(orgfile, startline, endline);
				final WitnessEdge edge = new WitnessEdge(source, target, data.getId(), loc, sourcecode);

				//@formatter:off
				final WitnessEdgeAnnotation annot = new WitnessEdgeAnnotation(
						transformControlToBooleanString(data.getProperties().get("control")),
						data.getProperties().get("enterLoopHead"),
						data.getProperties().get("enterFunction"),
						data.getProperties().get("returnFrom"),
						data.getProperties().get("tokens"),
						data.getProperties().get("assumption")
				);
				//@formatter:on
				if (!annot.isEmpty()) {
					annot.annotate(edge);
				}
				return edge;
			}

		};
	}

	private Transformer<NodeMetadata, WitnessNode> getVertexTransformer() {
		return new Transformer<NodeMetadata, WitnessNode>() {
			@Override
			public WitnessNode transform(final NodeMetadata data) {
				final WitnessNode node = createNode(data.getId());

				//@formatter:off
				final WitnessNodeAnnotation annot = new WitnessNodeAnnotation(
						getBoolProperty(data, "entry"),
						getBoolProperty(data, "violation"),
						getBoolProperty(data, "sink"),
						data.getProperties().get("invariant")
				);
				//@formatter:on

				if (!annot.isDefault()) {
					annot.annotate(node);
				}
				return node;
			}
		};
	}

	private Transformer<GraphMetadata, DirectedSparseGraph<WitnessNode, WitnessEdge>> getGraphTransformer() {
		return new Transformer<GraphMetadata, DirectedSparseGraph<WitnessNode, WitnessEdge>>() {

			@Override
			public DirectedSparseGraph<WitnessNode, WitnessEdge> transform(final GraphMetadata gm) {
				final String sourcecodelang = gm.getProperty("sourcecodelang");
				final WitnessType witnesstype = (WitnessType) getEnumProperty(WitnessGraphAnnotation.WitnessType.class,
						gm, "witness-type", WitnessGraphAnnotation.WitnessType.VIOLATION_WITNESS);
				mGraphAnnotation = new WitnessGraphAnnotation(sourcecodelang, witnesstype);

				final DirectedSparseGraph<WitnessNode, WitnessEdge> graph =
						new DirectedSparseGraph<WitnessNode, WitnessEdge>();
				for (final Entry<Object, NodeMetadata> e : gm.getNodeMap().entrySet()) {
					graph.addVertex((WitnessNode) e.getKey());
				}
				for (final Entry<Object, EdgeMetadata> e : gm.getEdgeMap().entrySet()) {
					final WitnessEdge edge = (WitnessEdge) e.getKey();
					graph.addEdge(edge, edge.getSource(), edge.getTarget());
				}
				return graph;
			}
		};
	}

	private String transformControlToBooleanString(final String controlString) {
		if (controlString == null) {
			return null;
		}
		if ("condition-true".equalsIgnoreCase(controlString)) {
			return "true";
		}
		if ("condition-false".equalsIgnoreCase(controlString)) {
			return "false";
		}
		throw new IllegalArgumentException("control cannot have this value: " + controlString);
	}

	private boolean getBoolProperty(final NodeMetadata data, final String key) {
		final String entry = data.getProperties().get(key);
		return entry != null && Boolean.valueOf(entry);
	}

	private <T extends Enum<T>> Enum<T> getEnumProperty(final Class<T> clazz, final AbstractMetadata data,
			final String key, final T defaultValue) {
		final String entry = data.getProperties().get(key);
		if (entry == null) {
			mLogger.warn("Your witness does not contain a value for " + key + " in element type "
					+ data.getMetadataType() + ". Assuming default value \"" + defaultValue + "\"");
			return defaultValue;
		}
		try {
			return Enum.valueOf(clazz, entry.toUpperCase());
		} catch (final IllegalArgumentException ex) {
			mLogger.error("Your witness contains an illegal value for " + key + " in element type "
					+ data.getMetadataType() + ": \"" + entry + "\". Assuming default value \"" + defaultValue + "\"");
			return defaultValue;
		}
	}

	private int getIntProperty(final EdgeMetadata data, final String key) {
		final String entry = data.getProperties().get(key);

		// set line to line if there is a valid line, -1 otherwise
		int value = 0;
		if (entry != null) {
			try {
				value = Integer.valueOf(entry);
			} catch (final Exception ex) {
				value = -1;
			}
		} else {
			value = -1;
		}
		return value;
	}

	private WitnessNode createNode(final String id) {
		WitnessNode node = mNodes.get(id);
		if (node == null) {
			node = new WitnessNode(id);
			mNodes.put(node.getName(), node);
		}
		return node;
	}

	public ModelType.Type getWitnessType() {
		return mWitnessType;
	}

}
