/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.witnessprinter;

import java.io.IOException;
import java.io.StringWriter;

import org.apache.commons.lang3.StringEscapeUtils;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.GeneratedWitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.GeneratedWitnessNode;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.GeneratedWitnessNodeEdgeFactory;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.UltimateGraphMLWriter;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.uci.ics.jung.graph.Hypergraph;

/**
 * Generates an SVCOMP witness from a {@link IProgramExecution} (i.e., a false witness). Probably only useful together
 * with {@link CACSLProgramExecution} instances.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 */
public class ViolationWitnessGenerator<TE, E> extends BaseWitnessGenerator<TE, E> {

	private final IProgramExecution<TE, E> mProgramExecution;
	private final IBacktranslationValueProvider<TE, E> mStringProvider;
	private final ILogger mLogger;

	public ViolationWitnessGenerator(final IProgramExecution<TE, E> translatedProgramExecution,
			final IBacktranslationValueProvider<TE, E> stringProvider, final ILogger logger,
			final IUltimateServiceProvider services) {
		super(services);
		assert translatedProgramExecution != null;
		assert translatedProgramExecution.getLength() > 0;
		mLogger = logger;
		mProgramExecution = translatedProgramExecution;
		mStringProvider = stringProvider;
	}

	@Override
	public String makeGraphMLString() {
		final UltimateGraphMLWriter<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graphWriter =
				new UltimateGraphMLWriter<>();
		final String filename = StringEscapeUtils
				.escapeXml10(mStringProvider.getFileNameFromStep(mProgramExecution.getTraceElement(0).getStep()));

		graphWriter.setEdgeIDs(arg0 -> arg0.getName());
		graphWriter.setVertexIDs(arg0 -> arg0.getName());

		addCanonicalWitnessGraphData(graphWriter, "violation_witness", filename);

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
		addVertexData(graphWriter, "invariant", "true", vertex -> null);

		final Hypergraph<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graph = getGraph();
		final StringWriter writer = new StringWriter();
		try {
			graphWriter.save(graph, writer);
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

	private Hypergraph<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> getGraph() {
		final DirectedSparseGraph<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graph =
				new OrderedDirectedSparseGraph<>();
		final GeneratedWitnessNodeEdgeFactory<TE, E> fac = new GeneratedWitnessNodeEdgeFactory<>(mStringProvider);

		GeneratedWitnessNode current = insertStartNodeAndDummyEdges(fac, graph, 0);
		GeneratedWitnessNode next;

		final int progExecLength = mProgramExecution.getLength();
		for (int idx = 0; idx < progExecLength; ++idx) {

			idx = collapseToSingleTraceElement(idx, mProgramExecution);

			final AtomicTraceElement<TE> currentATE = mProgramExecution.getTraceElement(idx);
			final ProgramState<E> currentState = mProgramExecution.getProgramState(idx);
			if (idx == progExecLength - 1) {
				// the last node is the error location
				next = fac.createErrorWitnessNode();
			} else {
				next = fac.createWitnessNode();
			}

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

	private GeneratedWitnessNode insertStartNodeAndDummyEdges(final GeneratedWitnessNodeEdgeFactory<TE, E> fac,
			final DirectedSparseGraph<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graph,
			final int numberOfUselessEdgesAfterStart) {
		GeneratedWitnessNode current = fac.createInitialWitnessNode();
		GeneratedWitnessNode next;
		graph.addVertex(current);

		for (int i = 0; i < numberOfUselessEdgesAfterStart; ++i) {
			next = fac.createWitnessNode();
			graph.addVertex(next);
			graph.addEdge(fac.createDummyWitnessEdge(), current, next);
			current = next;
		}

		return current;
	}

	private int collapseToSingleTraceElement(final int currentIdx, final IProgramExecution<TE, E> programExecution) {
		int i = currentIdx;
		for (; i < programExecution.getLength(); i++) {
			final AtomicTraceElement<TE> currentATE = programExecution.getTraceElement(i);
			final TE currentLoc = currentATE.getTraceElement();
			for (int j = i; j < programExecution.getLength(); j++) {
				final AtomicTraceElement<TE> nextATE = programExecution.getTraceElement(j);
				final TE nextLoc = nextATE.getTraceElement();

				if (mStringProvider.getStartLineNumberFromStep(nextLoc) != mStringProvider
						.getStartLineNumberFromStep(currentLoc)) {
					return j - 1;
				}
			}
		}
		return currentIdx;
	}
}
