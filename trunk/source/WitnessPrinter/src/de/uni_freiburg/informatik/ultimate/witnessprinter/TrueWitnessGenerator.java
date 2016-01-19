/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE WitnessPrinter plug-in.
 * 
 * The ULTIMATE WitnessPrinter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE WitnessPrinter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessPrinter plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessPrinter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE WitnessPrinter plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.witnessprinter;

import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.commons.collections15.Transformer;
import org.apache.commons.lang3.StringEscapeUtils;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.model.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.HoareAnnotation;
import de.uni_freiburg.informatik.ultimate.result.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.result.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.GeneratedWitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.GeneratedWitnessNode;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.GeneratedWitnessNodeEdgeFactory;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.uci.ics.jung.graph.Hypergraph;
import edu.uci.ics.jung.io.GraphMLWriter;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class TrueWitnessGenerator<TE, E> extends BaseWitnessGenerator<TE, E> implements IUnmanagedObserver {

	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;
	private Hypergraph<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> mGraph;

	public TrueWitnessGenerator(IUltimateServiceProvider services) {
		super();
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);

	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (root instanceof RootNode) {
			final RootNode rootNode = (RootNode) root;
			final IBacktranslationValueProvider<TE, E> stringProvider = null;
			final Map<RCFGNode, Expression> invariants = extractInvariants(rootNode);
			mGraph = getGraph(stringProvider, rootNode, invariants);
		}
		return false;
	}

	@Override
	public String makeGraphMLString() {
		final GraphMLWriter<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graphWriter = new GraphMLWriter<>();
		final String filename = StringEscapeUtils.escapeXml10("");
		// mStringProvider.getFileNameFromStep(mProgramExecution.getTraceElement(0).getStep())

		graphWriter.setEdgeIDs(new Transformer<GeneratedWitnessEdge<TE, E>, String>() {
			@Override
			public String transform(GeneratedWitnessEdge<TE, E> arg0) {
				return arg0.getName();
			}
		});

		graphWriter.setVertexIDs(new Transformer<GeneratedWitnessNode, String>() {
			@Override
			public String transform(GeneratedWitnessNode arg0) {
				return arg0.getName();
			}
		});

		addGraphData(graphWriter, "sourcecodelang", null, graph -> "C");
		addGraphData(graphWriter, "witness-type", null, graph -> "false_witness");

		addEdgeData(graphWriter, "sourcecode", null, edge -> StringEscapeUtils.escapeXml10(edge.getSourceCode()));
		addEdgeData(graphWriter, "assumption", null, edge -> StringEscapeUtils.escapeXml10(edge.getAssumption()));
		addEdgeData(graphWriter, "tokens", null, edge -> null);
		addEdgeData(graphWriter, "control", null, edge -> edge.getControl());
		addEdgeData(graphWriter, "startline", null, edge -> edge.getStartLineNumber());
		addEdgeData(graphWriter, "endline", null, edge -> edge.getEndLineNumber());
		addEdgeData(graphWriter, "originfile", filename, edge -> null);
		addEdgeData(graphWriter, "enterFunction", null, edge -> null);
		addEdgeData(graphWriter, "returnFrom", null, edge -> null);

		addVertexData(graphWriter, "nodetype", "path", vertex -> null);
		addVertexData(graphWriter, "entry", "false", vertex -> vertex.isEntry() ? "true" : null);
		addVertexData(graphWriter, "violation", "false", vertex -> vertex.isError() ? "true" : null);
		// TODO: When we switch to "multi-property" witnesses, we write invariants for FALSE-witnesses
		addVertexData(graphWriter, "invariant", "true", vertex -> vertex.getInvariant());

		final StringWriter writer = new StringWriter();
		try {
			graphWriter.save(mGraph, writer);
		} catch (final IOException e) {
			mLogger.error("Could not save witness graph: " + e.getMessage());
		}
		try {
			writer.flush();
			return writer.toString();
		} finally {
			try {
				writer.close();
			} catch (final IOException e) {
				mLogger.error("Could not close witness writer: " + e.getMessage());
			}
		}
	}

	private Hypergraph<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> getGraph(
			final IBacktranslationValueProvider<TE, E> stringProvider, final RootNode root,
			final Map<RCFGNode, Expression> invariants) {
		final DirectedSparseGraph<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graph = new OrderedDirectedSparseGraph<>();
		final GeneratedWitnessNodeEdgeFactory<TE, E> fac = new GeneratedWitnessNodeEdgeFactory<TE, E>(stringProvider);

		final Deque<RCFGNode> worklist = new ArrayDeque<>();
		final Map<RCFGNode, GeneratedWitnessNode> nodecache = new HashMap<>();
		final Set<RCFGEdge> closed = new HashSet<RCFGEdge>();

		GeneratedWitnessNode rootWitnessNode = fac.createInitialWitnessNode();
		nodecache.put(root, rootWitnessNode);
		graph.addVertex(rootWitnessNode);

		// initial edges are different
		for (final RCFGEdge outgoing : root.getOutgoingEdges()) {
			final GeneratedWitnessEdge<TE, E> edge = fac.createDummyWitnessEdge();
			final GeneratedWitnessNode node = getWitnessNode(outgoing.getTarget(), invariants, stringProvider, fac,
					nodecache);
			graph.addEdge(edge, rootWitnessNode, node);
			closed.add(outgoing);
			worklist.add(outgoing.getTarget());
		}

		// now for the rest
		while (!worklist.isEmpty()) {
			final RCFGNode sourceNode = worklist.remove();
			final GeneratedWitnessNode sourceWNode = getWitnessNode(sourceNode, invariants, stringProvider, fac,
					nodecache);

			for (final RCFGEdge outgoing : root.getOutgoingEdges()) {
				if (!closed.add(outgoing)) {
					continue;
				}
				final AtomicTraceElement<TE> traceElement = getATE(outgoing);
				final GeneratedWitnessEdge<TE, E> edge = fac.createWitnessEdge(traceElement);
				final GeneratedWitnessNode targetWNode = getWitnessNode(outgoing.getTarget(), invariants,
						stringProvider, fac, nodecache);

				graph.addEdge(edge, sourceWNode, targetWNode);
				worklist.add(outgoing.getTarget());
			}
		}

		return graph;
	}

	private AtomicTraceElement<TE> getATE(RCFGEdge outgoing) {
		// TODO Auto-generated method stub
		return null;
	}

	private GeneratedWitnessNode getWitnessNode(final RCFGNode node, final Map<RCFGNode, Expression> invariants,
			final IBacktranslationValueProvider<TE, E> stringProvider, final GeneratedWitnessNodeEdgeFactory<TE, E> fac,
			final Map<RCFGNode, GeneratedWitnessNode> nodecache) {
		GeneratedWitnessNode wnode = nodecache.get(node);
		if (wnode != null) {
			return wnode;
		}

		wnode = fac.createWitnessNode();
		nodecache.put(node, wnode);
		final Expression invariant = invariants.get(node);
		if (invariant == null) {
			return wnode;
		}

		// TODO: Translate invariant, set invariant
		wnode.setInvariant(invariant.toString());

		return wnode;
	}

	private Map<RCFGNode, Expression> extractInvariants(final RootNode root) {
		final RootAnnot rootAnnot = root.getRootAnnot();
		final IBacktranslationService backtranslator = mServices.getBacktranslationService();
		final Term trueTerm = rootAnnot.getScript().term("true");
		final Map<RCFGNode, Expression> rtr = new HashMap<RCFGNode, Expression>();

		// loop invariants
		for (final ProgramPoint locNode : rootAnnot.getLoopLocations().keySet()) {
			assert (locNode.getBoogieASTNode() != null) : "locNode without BoogieASTNode";

			final HoareAnnotation hoare = HoareAnnotation.getAnnotation(locNode);
			if (hoare == null) {
				continue;
			}
			final Term formula = hoare.getFormula();
			if (formula.equals(trueTerm)) {
				continue;
			}

			final Expression expr = rootAnnot.getBoogie2SMT().getTerm2Expression().translate(formula);
			mLogger.info("Invariant at " + locNode + " is "
					+ backtranslator.translateExpressionToString(expr, (Class<Expression>) expr.getClass()));
			final Expression old = rtr.put(locNode, expr);
			assert old == null : "Only one expression per node";
		}

		// procedure contracts
		for (final Entry<String, ProgramPoint> entry : rootAnnot.getExitNodes().entrySet()) {
			if (isAuxilliaryProcedure(entry.getKey())) {
				continue;
			}
			final HoareAnnotation hoare = HoareAnnotation.getAnnotation(entry.getValue());
			if (hoare == null) {
				continue;
			}
			final Term formula = hoare.getFormula();
			if (formula.equals(trueTerm)) {
				continue;
			}
			final Expression expr = rootAnnot.getBoogie2SMT().getTerm2Expression().translate(formula);
			mLogger.info("Contract at " + entry.getValue() + " is "
					+ backtranslator.translateExpressionToString(expr, (Class<Expression>) expr.getClass()));
			final Expression old = rtr.put(entry.getValue(), expr);
			assert old == null : "Only one expression per node";
		}

		return rtr;
	}

	private static boolean isAuxilliaryProcedure(final String proc) {
		return proc.equals("ULTIMATE.init") || proc.equals("ULTIMATE.start");
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) throws Throwable {

	}

	@Override
	public void finish() throws Throwable {

	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

}
