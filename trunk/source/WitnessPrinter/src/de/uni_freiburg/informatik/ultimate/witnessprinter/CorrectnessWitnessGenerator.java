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
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.StringEscapeUtils;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ConditionAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslatedCFG;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.GeneratedWitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.GeneratedWitnessNode;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.GeneratedWitnessNodeEdgeFactory;
import de.uni_freiburg.informatik.ultimate.witnessprinter.graphml.UltimateGraphMLWriter;
import de.uni_freiburg.informatik.ultimate.witnessprinter.preferences.PreferenceInitializer;
import edu.uci.ics.jung.graph.DirectedOrderedSparseMultigraph;
import edu.uci.ics.jung.graph.Hypergraph;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CorrectnessWitnessGenerator<TTE, TE> extends BaseWitnessGenerator<TTE, TE> {

	private static final String[] ACSL_SUBSTRING = new String[] { "\\old", "\\result", "\\exists" };

	private final ILogger mLogger;
	private final IBacktranslationValueProvider<TTE, TE> mStringProvider;
	private final IBacktranslatedCFG<?, TTE> mTranslatedCFG;
	private final boolean mIsACSLForbidden;

	@SuppressWarnings("unchecked")
	public CorrectnessWitnessGenerator(final IBacktranslatedCFG<?, TTE> translatedCFG, final ILogger logger,
			final IUltimateServiceProvider services) {
		super(services);
		mLogger = logger;
		mStringProvider = (IBacktranslationValueProvider<TTE, TE>) translatedCFG.getBacktranslationValueProvider();
		mTranslatedCFG = translatedCFG;
		mIsACSLForbidden =
				PreferenceInitializer.getPreferences(services).getBoolean(PreferenceInitializer.LABEL_DO_NOT_USE_ACSL);

	}

	@Override
	public String makeGraphMLString() {
		final UltimateGraphMLWriter<GeneratedWitnessNode, GeneratedWitnessEdge<TTE, TE>> graphWriter =
				new UltimateGraphMLWriter<>();
		graphWriter.setEdgeIDs(arg0 -> arg0.getName());
		graphWriter.setVertexIDs(arg0 -> arg0.getName());

		addCanonicalWitnessGraphData(graphWriter, "correctness_witness", mTranslatedCFG.getFilename());

		addEdgeData(graphWriter, "sourcecode", null, edge -> StringEscapeUtils.escapeXml10(edge.getSourceCode()));
		addEdgeData(graphWriter, "assumption", null, edge -> StringEscapeUtils.escapeXml10(edge.getAssumption()));
		addEdgeData(graphWriter, "tokens", null, edge -> null);
		addEdgeData(graphWriter, "control", null, edge -> edge.getControl());
		addEdgeData(graphWriter, "startline", null, edge -> edge.getStartLineNumber());
		addEdgeData(graphWriter, "endline", null, edge -> edge.getEndLineNumber());
		addEdgeData(graphWriter, "originfile", StringEscapeUtils.escapeXml10(mTranslatedCFG.getFilename()),
				edge -> null);
		addEdgeData(graphWriter, "enterFunction", null, edge -> null);
		addEdgeData(graphWriter, "returnFrom", null, edge -> null);
		addEdgeData(graphWriter, "enterLoopHead", "false", edge -> edge.isEnteringLoopHead());

		addVertexData(graphWriter, "nodetype", "path", vertex -> null);
		addVertexData(graphWriter, "entry", "false", vertex -> vertex.isEntry() ? "true" : null);
		addVertexData(graphWriter, "violation", "false", vertex -> vertex.isError() ? "true" : null);
		// TODO: When we switch to "multi-property" witnesses, we write invariants for FALSE-witnesses
		addVertexData(graphWriter, "invariant", "true", vertex -> StringEscapeUtils.escapeXml10(vertex.getInvariant()));

		final Hypergraph<GeneratedWitnessNode, GeneratedWitnessEdge<TTE, TE>> graph = getGraph();
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

	@SuppressWarnings("unchecked")
	private Hypergraph<GeneratedWitnessNode, GeneratedWitnessEdge<TTE, TE>> getGraph() {
		// cast is dirty hack because java does not allow casting s.t. TE is hidden (?!)
		final List<IExplicitEdgesMultigraph<?, ?, ?, TTE, ?>> roots =
				(List<IExplicitEdgesMultigraph<?, ?, ?, TTE, ?>>) (List<?>) mTranslatedCFG.getCFGs();
		if (roots.size() != 1) {
			throw new UnsupportedOperationException("Cannot generate correctness witnesses in library mode");
		}
		final IExplicitEdgesMultigraph<?, ?, ?, TTE, ?> root = roots.get(0);
		final Deque<IExplicitEdgesMultigraph<?, ?, ?, TTE, ?>> worklist = new ArrayDeque<>();
		final Map<IExplicitEdgesMultigraph<?, ?, ?, TTE, ?>, GeneratedWitnessNode> nodecache = new HashMap<>();
		final DirectedOrderedSparseMultigraph<GeneratedWitnessNode, GeneratedWitnessEdge<TTE, TE>> graph =
				new DirectedOrderedSparseMultigraph<>();
		final GeneratedWitnessNodeEdgeFactory<TTE, TE> fac = new GeneratedWitnessNodeEdgeFactory<>(mStringProvider);

		// add initial node to nodecache s.t. it will always be initial
		nodecache.put(root, annotateInvariant(root, fac.createInitialWitnessNode()));

		final Set<IMultigraphEdge<?, ?, ?, TTE, ?>> closed = new HashSet<>();
		worklist.add(root);

		while (!worklist.isEmpty()) {
			final IExplicitEdgesMultigraph<?, ?, ?, TTE, ?> sourceNode = worklist.remove();
			final GeneratedWitnessNode sourceWNode = getWitnessNode(sourceNode, mStringProvider, fac, nodecache);

			for (final IMultigraphEdge<?, ?, ?, TTE, ?> outgoing : sourceNode.getOutgoingEdges()) {
				if (!closed.add(outgoing)) {
					continue;
				}
				final TTE label = outgoing.getLabel();
				final GeneratedWitnessEdge<TTE, TE> edge;

				final GeneratedWitnessNode targetWNode =
						getWitnessNode(outgoing.getTarget(), mStringProvider, fac, nodecache);

				if (label == null) {
					edge = fac.createDummyWitnessEdge();
				} else {
					final ConditionAnnotation coan = ConditionAnnotation.getAnnotation(outgoing);

					final StepInfo stepInfo = coan != null
							? coan.isNegated() ? StepInfo.CONDITION_EVAL_FALSE : StepInfo.CONDITION_EVAL_TRUE
							: StepInfo.NONE;
					// it is a dirty hack that we say whenever our targetnode has an invariant the edge is a
					// enterLoopHead edge
					final boolean isEnteringLoopHead = targetWNode.getInvariant() != null;
					edge = fac.createWitnessEdge(new AtomicTraceElement<>(label, label, stepInfo, null),
							isEnteringLoopHead);
				}

				graph.addEdge(edge, sourceWNode, targetWNode);
				worklist.add(outgoing.getTarget());
			}
		}
		return graph;
	}

	private GeneratedWitnessNode getWitnessNode(final IExplicitEdgesMultigraph<?, ?, ?, TTE, ?> node,
			final IBacktranslationValueProvider<TTE, TE> stringProvider,
			final GeneratedWitnessNodeEdgeFactory<TTE, TE> fac,
			final Map<IExplicitEdgesMultigraph<?, ?, ?, TTE, ?>, GeneratedWitnessNode> nodecache) {
		GeneratedWitnessNode wnode = nodecache.get(node);
		if (wnode != null) {
			return wnode;
		}
		wnode = annotateInvariant(node, fac.createWitnessNode());
		nodecache.put(node, wnode);
		return wnode;
	}

	private GeneratedWitnessNode annotateInvariant(final IExplicitEdgesMultigraph<?, ?, ?, TTE, ?> node,
			final GeneratedWitnessNode wnode) {
		final String invariant = filterInvariant(node);
		if (invariant != null) {
			wnode.setInvariant(invariant);
		}
		return wnode;
	}

	private String filterInvariant(final IExplicitEdgesMultigraph<?, ?, ?, TTE, ?> node) {
		if (node == null) {
			return null;
		}
		if (node.getLabel() == null) {
			return null;
		}
		final String label = node.getLabel().toString();
		if (mIsACSLForbidden && label != null && Arrays.stream(ACSL_SUBSTRING).anyMatch(label::contains)) {
			mLogger.warn("Not writing invariant because ACSL is forbidden: " + label);
			return null;
		}
		return label;
	}
}
