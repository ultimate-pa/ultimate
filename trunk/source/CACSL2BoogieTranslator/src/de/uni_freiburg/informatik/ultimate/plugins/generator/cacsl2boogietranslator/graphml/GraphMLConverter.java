package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.graphml;

import java.io.IOException;
import java.io.StringWriter;
import java.util.LinkedHashMap;
import java.util.Map;

import org.apache.commons.collections15.Transformer;
import org.apache.commons.lang3.StringEscapeUtils;
import org.eclipse.cdt.core.dom.ast.IASTExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSLProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.uci.ics.jung.graph.Hypergraph;
import edu.uci.ics.jung.graph.util.Pair;
import edu.uci.ics.jung.io.GraphMLWriter;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class GraphMLConverter {

	private final CACSLProgramExecution mProgramExecution;

	public GraphMLConverter(CACSLProgramExecution translatedProgramExecution) {
		assert translatedProgramExecution != null;
		assert translatedProgramExecution.getLength() > 0;
		mProgramExecution = translatedProgramExecution;
	}

	public String makeGraphMLString() {
		StringWriter writer = new StringWriter();

		GraphMLWriter<WitnessNode, WitnessEdge> graphWriter = new GraphMLWriter<>();
		String filename = StringEscapeUtils.escapeXml10(mProgramExecution.getTraceElement(0).getStep().getFileName());
		graphWriter.setEdgeIDs(new Transformer<WitnessEdge, String>() {
			@Override
			public String transform(WitnessEdge arg0) {
				return arg0.getName();
			}
		});

		graphWriter.setVertexIDs(new Transformer<WitnessNode, String>() {
			@Override
			public String transform(WitnessNode arg0) {
				return arg0.getName();
			}
		});

		graphWriter.addGraphData("sourcecodelang", null, null,
				new Transformer<Hypergraph<WitnessNode, WitnessEdge>, String>() {
					@Override
					public String transform(Hypergraph<WitnessNode, WitnessEdge> arg0) {
						return "C";
					}
				});

		graphWriter.addEdgeData("sourcecode", null, null, new Transformer<WitnessEdge, String>() {
			@Override
			public String transform(WitnessEdge arg0) {
				return StringEscapeUtils.escapeXml10(arg0.getSourceCode());
			}
		});

		graphWriter.addEdgeData("assumption", null, null, new Transformer<WitnessEdge, String>() {
			@Override
			public String transform(WitnessEdge arg0) {
				return StringEscapeUtils.escapeXml10(arg0.getAssumption());
			}
		});

		graphWriter.addEdgeData("tokens", null, null, new Transformer<WitnessEdge, String>() {
			@Override
			public String transform(WitnessEdge arg0) {
				return null;
			}
		});

		graphWriter.addEdgeData("negated", null, "false", new Transformer<WitnessEdge, String>() {
			@Override
			public String transform(WitnessEdge arg0) {
				if (arg0.isNegated()) {
					return "true";
				}
				return null;
			}
		});

		graphWriter.addEdgeData("originline", null, null, new Transformer<WitnessEdge, String>() {
			@Override
			public String transform(WitnessEdge arg0) {
				return arg0.getLineNumber();
			}
		});

		graphWriter.addEdgeData("originfile", null, filename, new Transformer<WitnessEdge, String>() {
			@Override
			public String transform(WitnessEdge arg0) {
				return null;
			}
		});

		graphWriter.addEdgeData("enterFunction", null, null, new Transformer<WitnessEdge, String>() {
			@Override
			public String transform(WitnessEdge arg0) {
				return null;
			}
		});

		graphWriter.addEdgeData("returnFrom", null, null, new Transformer<WitnessEdge, String>() {
			@Override
			public String transform(WitnessEdge arg0) {
				return null;
			}
		});

		graphWriter.addVertexData("nodetype", null, "path", new Transformer<WitnessNode, String>() {
			@Override
			public String transform(WitnessNode arg0) {
				return null;
			}
		});

		graphWriter.addVertexData("entry", null, "false", new Transformer<WitnessNode, String>() {
			@Override
			public String transform(WitnessNode arg0) {
				if (arg0.isEntry()) {
					return "true";
				}
				return null;
			}
		});

		Hypergraph<WitnessNode, WitnessEdge> graph = getGraph();

		try {
			graphWriter.save(graph, writer);
		} catch (IOException e) {
			e.printStackTrace();
		}
		try {
			writer.flush();
			return writer.toString();
		} finally {
			try {
				writer.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	// private Hypergraph<WitnessNode, WitnessEdge> getGraph() {
	// DirectedSparseGraph<WitnessNode, WitnessEdge> graph = new
	// DirectedSparseGraph<>();
	// WitnessNodeEdgeFactory fac = new WitnessNodeEdgeFactory();
	//
	// WitnessNode current = insertStartNodeAndDummyEdges(fac, graph, 0);
	// WitnessNode next = null;
	//
	// // Looks like they use assumptions before their statements, so why not
	// // ...
	// ProgramState<IASTExpression> assumptionState = null;
	//
	// for (int i = 0; i < mProgramExecution.getLength(); ++i) {
	//
	// i = skipGlobalDeclarations(i, mProgramExecution);
	// i = collapseToSingleTraceElement(i, mProgramExecution);
	// if (i == 0) {
	// //we only use our initial state if we did not skip initial states
	// assumptionState = mProgramExecution.getInitialProgramState();
	// }
	//
	// AtomicTraceElement<CACSLLocation> currentATE =
	// mProgramExecution.getTraceElement(i);
	// next = fac.createWitnessNode();
	// graph.addVertex(next);
	// if (assumptionState == null) {
	// graph.addEdge(fac.createWitnessEdge(currentATE), current, next);
	// } else {
	// graph.addEdge(fac.createWitnessEdge(currentATE, assumptionState),
	// current, next);
	// }
	// current = next;
	// assumptionState = mProgramExecution.getProgramState(i);
	// }
	//
	// return graph;
	// }

	private Hypergraph<WitnessNode, WitnessEdge> getGraph() {
		DirectedSparseGraph<WitnessNode, WitnessEdge> graph = new OrderedDirectedSparseGraph<>();
		WitnessNodeEdgeFactory fac = new WitnessNodeEdgeFactory();

		WitnessNode current = insertStartNodeAndDummyEdges(fac, graph, 0);
		WitnessNode next = null;

		// Add initial state edge if present; only edge with assumption but no
		// source code or line number
		ProgramState<IASTExpression> initialState = mProgramExecution.getInitialProgramState();
		if (initialState != null) {
			next = fac.createWitnessNode();
			graph.addVertex(next);
			graph.addEdge(fac.createWitnessEdge(initialState), current, next);
			current = next;
		}

		for (int i = 0; i < mProgramExecution.getLength(); ++i) {

			// i = skipGlobalDeclarations(i, mProgramExecution);
			i = collapseToSingleTraceElement(i, mProgramExecution);

			AtomicTraceElement<CACSLLocation> currentATE = mProgramExecution.getTraceElement(i);
			ProgramState<IASTExpression> currentState = mProgramExecution.getProgramState(i);
			next = fac.createWitnessNode();
			graph.addVertex(next);
			if (currentState == null) {
				graph.addEdge(fac.createWitnessEdge(currentATE), current, next);
			} else {
				graph.addEdge(fac.createWitnessEdge(currentATE, currentState), current, next);
			}
			current = next;
		}

		return graph;
	}

	private WitnessNode insertStartNodeAndDummyEdges(WitnessNodeEdgeFactory fac,
			DirectedSparseGraph<WitnessNode, WitnessEdge> graph, int numberOfUselessEdgesAfterStart) {
		WitnessNode current = fac.createWitnessNode(true);
		WitnessNode next = null;
		graph.addVertex(current);

		for (int i = 0; i < numberOfUselessEdgesAfterStart; ++i) {
			next = fac.createWitnessNode();
			graph.addVertex(next);
			graph.addEdge(fac.createDummyWitnessEdge(), current, next);
			current = next;
		}

		return current;
	}

	// private int skipGlobalDeclarations(int currentIdx, CACSLProgramExecution
	// programExecution) {
	// int i = currentIdx;
	// for (; i < programExecution.getLength(); i++) {
	// AtomicTraceElement<CACSLLocation> currentATE =
	// programExecution.getTraceElement(i);
	// CACSLLocation currentLoc = currentATE.getTraceElement();
	// if (currentLoc instanceof CLocation) {
	// CLocation currentCLoc = (CLocation) currentLoc;
	// if (currentCLoc.getNode() instanceof CASTSimpleDeclaration) {
	// if (currentCLoc.getNode().getParent() instanceof CASTTranslationUnit) {
	// // it is a global, go on
	// continue;
	// }
	// }
	// }
	// break;
	// }
	// return i;
	// }

	private int collapseToSingleTraceElement(int currentIdx, CACSLProgramExecution programExecution) {
		int i = currentIdx;
		for (; i < programExecution.getLength(); i++) {
			AtomicTraceElement<CACSLLocation> currentATE = programExecution.getTraceElement(i);
			CACSLLocation currentLoc = currentATE.getTraceElement();
			for (int j = i; j < programExecution.getLength(); j++) {
				AtomicTraceElement<CACSLLocation> nextATE = programExecution.getTraceElement(j);
				CACSLLocation nextLoc = nextATE.getTraceElement();
				if (nextLoc.getStartLine() != currentLoc.getStartLine()) {
					return j - 1;
				}
			}
		}
		return currentIdx;
	}

	/**
	 * Change the default {@link DirectedSparseGraph} s.t. the nodes and edges
	 * written are ordered lexicographically. DirectedSparseGraph
	 * 
	 * @author dietsch@informatik.uni-freiburg.de
	 */
	private class OrderedDirectedSparseGraph<V, E> extends DirectedSparseGraph<V, E> {
		private static final long serialVersionUID = -8539872407688620571L;

		public OrderedDirectedSparseGraph() {
			super();
			vertices = new LinkedHashMap<V, Pair<Map<V, E>>>();
			edges = new LinkedHashMap<>();
		}
	}
}
