package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

public class PowersetConstruction {

	private final Script mScript;
	private final GuardGraph mGuardGraph;
	private final ILogger mLogger;

	public PowersetConstruction(ILogger logger, List<GuardGraph> automata, Script script) {
		mLogger = logger;
		mScript = script;
		// take first automaton from list
		GuardGraph prodAut = automata.get(0);
		// remove first automaton from list
		automata.remove(0);
		// iterate over the remaining automata
		for (GuardGraph auto : automata) {
			// create cut automaton between taken automaton and one automaton from list
			GuardGraph prodOfTwo = makeProductOfTwoAutomata(prodAut, auto);
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
	 * a helper modulo operation to find A = {0...n}, B = {0...m} given i from A and
	 * j from B nodeId = i * |B| + j
	 */
	private int getNodeIndex(int idNode1, int idNode2, int sizeOfB) {
		return idNode1 * sizeOfB + idNode2;
	}

	private GuardGraph makeProductOfTwoAutomata(GuardGraph auto1, GuardGraph auto2) {

		final Set<GuardGraph> auto1Nodes = auto1.getAllNodes();
		final Set<GuardGraph> auto2Nodes = auto2.getAllNodes();

		final Map<Integer, GuardGraph> newStates = new HashMap<Integer, GuardGraph>();
		for (GuardGraph v1 : auto1Nodes) {
			for (GuardGraph v2 : auto2Nodes) {
				int index = getNodeIndex(v1.getLabel(), v2.getLabel(), auto2Nodes.size());
				newStates.put(index, new GuardGraph(index));
			}
		}
		/*
		 * let G1 = (V1, R1), let G2 = (V2, R2) (v, X, v') element G1 (w, Y, w') element
		 * G2 (v, X, v') x (w, Y, w') = (vw, X and Y, v'w')
		 * 
		 * Startnode = vw also (findTheNode(v, w, sizeOf(V2)) Endnode = v'w' also
		 * (findTheNode(v', w', sizeOf(V2))
		 */
		Term conjTerm;
		Term X;
		Term Y;
		for (GuardGraph v : auto1Nodes) {
			for (GuardGraph vl : auto1Nodes) {
				// take the term, now we have (v, X, v')
				if (v.getOutgoingNodes().contains(vl)) {
					X = v.getOutgoingEdgeLabel(vl);
				} else {
					continue;
				}
				// now for the second term and tuple
				for (GuardGraph w : auto2Nodes) {
					for (GuardGraph wl : auto2Nodes) {
						// take the term, now we have (w, Y, w')
						if (w.getOutgoingNodes().contains(wl)) {
							Y = w.getOutgoingEdgeLabel(wl);
						} else {
							continue;
						}
						int fromIndex = getNodeIndex(v.getLabel(), w.getLabel(), auto2Nodes.size());
						int toIndex = getNodeIndex(vl.getLabel(), wl.getLabel(), auto2Nodes.size());
						conjTerm = SmtUtils.and(mScript, X, Y);
						if (!SmtUtils.isFalse(conjTerm))
							newStates.get(fromIndex).connectOutgoing(newStates.get(toIndex), conjTerm);

					}
				}
			}
		}
		return newStates.get(0);
	}
}
