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
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

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

	private final IProgramExecution<TE, E> mStem;
	private final IProgramExecution<TE, E> mLoop;
	private final IBacktranslationValueProvider<TE, E> mStringProvider;
	private final ILogger mLogger;

	/**
	 * Use this constructor if you want to construct a witness for the violation of a reachability property.
	 */
	public ViolationWitnessGenerator(final IProgramExecution<TE, E> stem, final ILogger logger,
			final IUltimateServiceProvider services) {
		super(services);
		assert stem != null;
		assert stem.getLength() > 0;
		mLogger = logger;
		mStem = stem;
		mStringProvider = stem.getBacktranslationValueProvider();
		mLoop = null;
	}

	/**
	 * Use this constructor if you want to construct a witness for the violation of a liveness property.
	 */
	public ViolationWitnessGenerator(final IProgramExecution<TE, E> stem, final IProgramExecution<TE, E> loop,
			final ILogger logger, final IUltimateServiceProvider services) {
		super(services);
		assert stem != null;
		assert loop != null;
		assert stem.getLength() > 0;
		assert loop.getLength() > 0;
		mLogger = logger;
		mStem = stem;
		mLoop = loop;
		mStringProvider = stem.getBacktranslationValueProvider();

	}

	@Override
	public String makeGraphMLString() {
		final UltimateGraphMLWriter<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graphWriter =
				new UltimateGraphMLWriter<>();
		final String filename =
				StringEscapeUtils.escapeXml10(mStringProvider.getFileNameFromStep(mStem.getTraceElement(0).getStep()));

		graphWriter.setEdgeIDs(GeneratedWitnessEdge<TE, E>::getName);
		graphWriter.setVertexIDs(GeneratedWitnessNode::getName);

		addCanonicalWitnessGraphData(graphWriter, "violation_witness", filename);

		addEdgeData(graphWriter, "sourcecode", null, edge -> StringEscapeUtils.escapeXml10(edge.getSourceCode()));
		addEdgeData(graphWriter, "assumption", null, edge -> StringEscapeUtils.escapeXml10(edge.getAssumption()));
		addEdgeData(graphWriter, "tokens", null, edge -> null);
		addEdgeData(graphWriter, "control", null, GeneratedWitnessEdge<TE, E>::getControl);
		addEdgeData(graphWriter, "startline", null, GeneratedWitnessEdge<TE, E>::getStartLineNumber);
		addEdgeData(graphWriter, "endline", null, GeneratedWitnessEdge<TE, E>::getEndLineNumber);
		addEdgeData(graphWriter, "originfile", filename, GeneratedWitnessEdge<TE, E>::getOriginFileName);
		addEdgeData(graphWriter, "enterFunction", null, GeneratedWitnessEdge<TE, E>::getEnterFunction);
		addEdgeData(graphWriter, "returnFrom", null, GeneratedWitnessEdge<TE, E>::getReturnFunction);
		addEdgeData(graphWriter, "enterLoopHead", "false", edge -> edge.isEnteringLoopHead());

		addVertexData(graphWriter, "nodetype", "path", vertex -> null);
		addVertexData(graphWriter, "entry", "false", vertex -> vertex.isEntry() ? "true" : null);
		addVertexData(graphWriter, "violation", "false", vertex -> vertex.isError() ? "true" : null);
		addVertexData(graphWriter, "cyclehead", "false", vertex -> vertex.isHonda() ? "true" : null);

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

		final IProgramExecution<TE, E> reducedStem = reduceProgramExecution(mStem);
		final IProgramExecution<TE, E> reducedLoop = mLoop == null ? null : reduceProgramExecution(mLoop);

		final GeneratedWitnessNode current = insertStartNodeAndDummyEdges(fac, graph, 0);
		final Supplier<GeneratedWitnessNode> funCreateLastNode;
		if (reducedLoop == null) {
			// if we have only a stem just create an error node as the last node of the stem
			funCreateLastNode = () -> fac.createErrorWitnessNode();
			addProgramExecution(graph, fac, current, reducedStem, funCreateLastNode);
		} else {
			// if we have stem and loop, the last node of the stem is the honda, and the honda is the first and last
			// node of the loop
			final GeneratedWitnessNode honda = fac.createHondaWitnessNode();
			funCreateLastNode = () -> honda;
			addProgramExecution(graph, fac, current, reducedStem, funCreateLastNode);
			addProgramExecution(graph, fac, honda, reducedLoop, funCreateLastNode);
		}

		return graph;
	}

	private void addProgramExecution(final DirectedSparseGraph<GeneratedWitnessNode, GeneratedWitnessEdge<TE, E>> graph,
			final GeneratedWitnessNodeEdgeFactory<TE, E> fac, GeneratedWitnessNode current,
			final IProgramExecution<TE, E> reducedStem, final Supplier<GeneratedWitnessNode> funCreateLastNode) {
		GeneratedWitnessNode next;
		final int progExecLength = reducedStem.getLength();
		for (int idx = 0; idx < progExecLength; ++idx) {

			final AtomicTraceElement<TE> currentATE = reducedStem.getTraceElement(idx);
			final ProgramState<E> currentState = reducedStem.getProgramState(idx);
			if (idx == progExecLength - 1) {
				next = funCreateLastNode.get();
			} else {
				next = fac.createWitnessNode();
			}

			graph.addVertex(next);
			graph.addEdge(fac.createWitnessEdge(currentATE, currentState, next.isHonda()), current, next);
			current = next;
		}
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

	private IProgramExecution<TE, E> reduceProgramExecution(final IProgramExecution<TE, E> origPe) {
		final List<AtomicTraceElement<TE>> trace = new ArrayList<>();
		final Map<Integer, ProgramState<E>> partialProgramStateMapping = new HashMap<>();

		partialProgramStateMapping.put(-1, origPe.getInitialProgramState());

		final int progExecLength = origPe.getLength();

		int newIdx = 0;

		for (int idx = 0; idx < progExecLength;) {
			final int oldIdx = idx;
			final AtomicTraceElement<TE> currentATE = origPe.getTraceElement(idx);
			trace.add(currentATE);
			partialProgramStateMapping.put(newIdx, origPe.getProgramState(idx));
			newIdx++;
			for (int j = idx + 1; j < progExecLength; ++j) {
				final AtomicTraceElement<TE> nextATE = origPe.getTraceElement(j);
				if (mStringProvider.getStartLineNumberFromStep(currentATE.getTraceElement()) != mStringProvider
						.getStartLineNumberFromStep(nextATE.getTraceElement())) {
					idx = j;
					break;
				}
			}

			if (oldIdx == idx) {
				break;
			}
		}

		return new ReducedProgramExecution<>(origPe, trace, partialProgramStateMapping);
	}

	private static final class ReducedProgramExecution<TE, E> implements IProgramExecution<TE, E> {

		private final List<AtomicTraceElement<TE>> mTrace;
		private final Map<Integer, ProgramState<E>> mPartialProgramStateMapping;
		private final IProgramExecution<TE, E> mOriginalProgramExecution;

		public ReducedProgramExecution(final IProgramExecution<TE, E> origPE, final List<AtomicTraceElement<TE>> trace,
				final Map<Integer, ProgramState<E>> partialProgramStateMapping) {
			mOriginalProgramExecution = origPE;
			mTrace = trace;
			mPartialProgramStateMapping = partialProgramStateMapping;
		}

		@Override
		public int getLength() {
			return mTrace.size();
		}

		@Override
		public AtomicTraceElement<TE> getTraceElement(final int index) {
			return mTrace.get(index);
		}

		@Override
		public ProgramState<E> getProgramState(final int index) {
			if (index < 0 || index >= mTrace.size()) {
				throw new IllegalArgumentException("out of range");
			}
			return mPartialProgramStateMapping.get(index);
		}

		@Override
		public ProgramState<E> getInitialProgramState() {
			return mPartialProgramStateMapping.get(-1);
		}

		@Override
		public Class<E> getExpressionClass() {
			return mOriginalProgramExecution.getExpressionClass();
		}

		@Override
		public Class<TE> getTraceElementClass() {
			return mOriginalProgramExecution.getTraceElementClass();
		}

		@Override
		public IBacktranslationValueProvider<TE, E> getBacktranslationValueProvider() {
			return mOriginalProgramExecution.getBacktranslationValueProvider();
		}
	}

}
