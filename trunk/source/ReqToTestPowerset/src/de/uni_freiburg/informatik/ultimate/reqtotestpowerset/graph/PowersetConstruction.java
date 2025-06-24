package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class PowersetConstruction {

	private final Script mScript;
	private final GuardGraph mGuardGraph;
	private final ILogger mLogger;
	private Map<Integer, GuardGraph> mProductAutStates;

	public PowersetConstruction(final ILogger logger, final List<GuardGraph> automata, final Script script) {
		mLogger = logger;
		mScript = script;
		// take first automaton from list
		GuardGraph prodAut = automata.get(0);
		// remove first automaton from list
		automata.remove(0);
		// iterate over the remaining automata
		for (final GuardGraph auto : automata) {
			// create cut automaton between taken automaton and one automaton from list
			final GuardGraph prodOfTwo = makeProductOfTwoAutomata(prodAut, auto);
			// resulted product of 2 automata is now the left term for the next round of
			// product
			// TODO maybe need to copy/clone the prodOfTwo to prodAut... need to research
			// this further
			prodAut = prodOfTwo;
		}
		mGuardGraph = prodAut;
	}

	public GuardGraph getProduct() {
		return mGuardGraph;
	}

	/*
	 * a helper modulo operation to find the equivalent resulting node given A = {0...n} and B = {0...m} where i from A
	 * and j from B
	 *
	 * resultingNodeId = i * |B| + j
	 */
	private int getNodeIndex(final int idNode1, final int idNode2, final int sizeOfB) {
		return idNode1 * sizeOfB + idNode2;
	}

	private void makeNodesForProductAutomat(final Set<GuardGraph> leftAutNodes, final Set<GuardGraph> rightAutNodes) {
		mProductAutStates = new HashMap<>();
		for (final GuardGraph v1 : leftAutNodes) {
			for (final GuardGraph v2 : rightAutNodes) {
				final int index = getNodeIndex(v1.getLabel(), v2.getLabel(), rightAutNodes.size());
				mProductAutStates.put(index, new GuardGraph(index));
			}
		}
	}

	private void makeProductFromRightAutomaton(final int v, final int vl, final Term X,
			final Set<GuardGraph> auto2Nodes) {
		Term Y;
		Term conjTerm;
		for (final GuardGraph w : auto2Nodes) {
			for (final GuardGraph wl : auto2Nodes) {
				// take the term, now we have (w, Y, w')
				if (w.getOutgoingNodes().contains(wl)) {
					Y = w.getOutgoingEdgeLabel(wl);
				} else {
					continue;
				}
				final int fromIndex = getNodeIndex(v, w.getLabel(), auto2Nodes.size());
				final int toIndex = getNodeIndex(vl, wl.getLabel(), auto2Nodes.size());
				conjTerm = SmtUtils.and(mScript, X, Y);
				if (!SmtUtils.isFalseLiteral(conjTerm)) {
					mProductAutStates.get(fromIndex).connectOutgoing(mProductAutStates.get(toIndex), conjTerm);
				}
				mProductAutStates.get(0).incEdges();
			}
		}
	}

	private GuardGraph makeProductOfTwoAutomata(final GuardGraph auto1, final GuardGraph auto2) {

		final Set<GuardGraph> auto1Nodes = auto1.getAllNodes();
		final Set<GuardGraph> auto2Nodes = auto2.getAllNodes();

		makeNodesForProductAutomat(auto1Nodes, auto2Nodes);

		/*
		 * let G1 = (V1, R1), let G2 = (V2, R2) (v, X, v') element G1 (w, Y, w') element G2 (v, X, v') x (w, Y, w') =
		 * (vw, X and Y, v'w')
		 *
		 * Startnode = vw also (findTheNode(v, w, sizeOf(V2)) Endnode = v'w' also (findTheNode(v', w', sizeOf(V2))
		 */

		Term X;
		for (final GuardGraph v : auto1Nodes) {
			for (final GuardGraph vl : auto1Nodes) {
				// take the term, now we have (v, X, v')
				if (v.getOutgoingNodes().contains(vl)) {
					X = v.getOutgoingEdgeLabel(vl);
				} else {
					continue;
				}
				// now for the second term and tuple
				makeProductFromRightAutomaton(v.getLabel(), vl.getLabel(), X, auto2Nodes);
			}
		}
		return mProductAutStates.get(0);
	}
}
