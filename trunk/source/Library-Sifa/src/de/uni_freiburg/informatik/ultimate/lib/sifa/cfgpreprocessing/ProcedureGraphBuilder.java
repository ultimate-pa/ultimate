/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

/**
 * Creates {@link ProcedureGraph}s from ICFGs.
 *
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @see #graphOfProcedure(String, Collection)
 */
public class ProcedureGraphBuilder {

	private final SifaStats mStats;
	private final IIcfg<IcfgLocation> mIcfg;
	private ProcedureGraph mCurrentProcedureGraph;
	private final Queue<IcfgLocation> mWork = new ArrayDeque<>();
	private final Set<IcfgLocation> mVisited = new HashSet<>();

	public ProcedureGraphBuilder(final SifaStats stats, final IIcfg<IcfgLocation> icfg) {
		mStats = stats;
		mIcfg = icfg;
	}

	/**
	 * Constructs a procedure graph for a given procedure.
	 * The resulting procedure graph is labeled with edges and nodes from its ICFG.
	 * Only relevant parts are included. Relevant parts are
	 * <ul>
	 *   <li> The procedure's entry node
	 *   <li> The procedure's exit node
	 *   <li> {@code locationsOfInterest}
	 *   <li> {@code enterCallsOfInterest}
	 *   <li> Everything connecting any of the above nodes
	 * </ul>
	 * <p>
	 * Inside the procedure graph calls are represented as follows:
	 * <ul>
	 *   <li> Calls to implemented procedures are represented by up to two edges.
	 *     <ul>
	 *       <li> One summary edge of type {@link CallReturnSummary} for the case in which we
	 *            enter the function and return normally.<br>
	 *            Note that summary edges do not actually summarize the call.
	 *            They are just there to point out, that we skipped the procedure.
	 *       <li> If requested by {@code enterCallsOfInterest}:
	 *            One error edge of type {@link IIcfgCallTransition} for the case in which we
	 *            enter the function but do not return due to errors in the callee or functions called by the callee.
	 *     </ul>
	 *   <li> Calls to unimplemented procedures are represented by the original summary edge from the icfg.
	 * </ul>
	 * Cases in which callees do not terminate are not treated specially.
	 *
	 * @param procedureName Name of the procedure for which a procedure graph shall be constructed
	 * @param locationsOfInterest Locations to be included in the graph
	 *                            besides the procedure's entry and exit location and connections between them.
	 * @param enterCallsOfInterest Names of the callees for which dead-end edges should be inserted
	 *                             modelling entering the callee without returning due to an error
	 */
	public ProcedureGraph graphOfProcedure(final String procedureName,
			final Collection<IcfgLocation> locationsOfInterest,
			final Collection<String> enterCallsOfInterest) {

		mStats.start(SifaStats.Key.PROCEDURE_GRAPH_BUILDER_TIME);

		mCurrentProcedureGraph = new ProcedureGraph(mIcfg, procedureName);
		// make sure that LOIs exist, even if they don't have any incoming or outgoing edges
		// (entry and exit are already added in the graph's constructor)
		locationsOfInterest.forEach(mCurrentProcedureGraph::addNode);
		enterCallsOfInterest.forEach(callee -> copyEnterCallEdges(procedureName, callee));

		mWork.add(mCurrentProcedureGraph.getExitNode());
		mWork.addAll(locationsOfInterest);
		while (!mWork.isEmpty()) {
			for (final IcfgEdge edge : mWork.remove().getIncomingEdges()) {
				processBottomUp(edge);
			}
		}
		mVisited.clear();
		mWork.clear();

		mStats.stop(SifaStats.Key.PROCEDURE_GRAPH_BUILDER_TIME);

		return mCurrentProcedureGraph;
	}

	@SuppressWarnings("unchecked")
	private void copyEnterCallEdges(final String caller, final String callee) {
		mIcfg.getProcedureEntryNodes().get(callee).getIncomingEdges().stream()
			.filter(incomingEdge -> incomingEdge instanceof IIcfgCallTransition<?>)
			.map(callEdge -> (IIcfgCallTransition<IcfgLocation>) callEdge)
			.filter(callEdge -> caller.equals(callEdge.getPrecedingProcedure()))
			// Dead end edge representing the possibility to enter the callee without returning due to an error
			.peek(this::copyEdge)
			.map(IIcfgTransition::getSource)
			.forEach(this::addToWorklistIfNew);
		// Call summaries are added later if needed
	}

	/**
	 * Traverses the ICFG backwards and copies edges to the procedure graph.
	 * Backwards processing allows to only include required paths (for instance to the procedure's exit or
	 * locations of interest) while ignoring dead ends in which we are not interested.
	 */
	@SuppressWarnings("unchecked")
	private void processBottomUp(final IcfgEdge edge) {
		if (edge instanceof IIcfgReturnTransition<?,?>) {
			processReturn((IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>>) edge);
		} else if (edge instanceof IIcfgCallTransition<?>) {
			processCall((IIcfgCallTransition<IcfgLocation>) edge);
		} else if (edge instanceof IIcfgSummaryTransition<?>) {
			processCallSummary((IIcfgSummaryTransition<IcfgLocation>) edge);
		} else {
			addToWorklistIfNew(edge.getSource());
			copyEdge(edge);
		}
	}

	private void processReturn(final IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> returnEdge) {
		final IIcfgCallTransition<IcfgLocation> correspondingCallEdge = returnEdge.getCorrespondingCall();
		final IcfgLocation correspondingSource = correspondingCallEdge.getSource();
		addToWorklistIfNew(correspondingSource);
		// Summary representing entering, executing the body, and returning from the callee in one step
		mCurrentProcedureGraph.addEdge(correspondingSource, new CallReturnSummary(returnEdge), returnEdge.getTarget());
		// Enter calls are only added if needed, see #copyEnterCallEdges
	}

	private void processCall(final IIcfgCallTransition<IcfgLocation> callEdge) {
		assert callEdge.getTarget() == mCurrentProcedureGraph.getEntryNode() :
				"Builder entered return (backwards) but should have skipped body of sub-procedure.";
	}

	private void processCallSummary(final IIcfgSummaryTransition<IcfgLocation> callSummaryEdge) {
		if (callSummaryEdge.calledProcedureHasImplementation()) {
			// nothing to do, we insert our own summary based on the return transition
			return;
		}
		mCurrentProcedureGraph.addEdge(callSummaryEdge.getSource(), callSummaryEdge, callSummaryEdge.getTarget());
		addToWorklistIfNew(callSummaryEdge.getSource());
	}

	private void addToWorklistIfNew(final IcfgLocation node) {
		if (!mVisited.contains(node)) {
			mVisited.add(node);
			mWork.add(node);
		}
	}

	private void copyEdge(final IIcfgTransition<IcfgLocation> edge) {
		mCurrentProcedureGraph.addEdge(edge.getSource(), edge, edge.getTarget());
	}
}
