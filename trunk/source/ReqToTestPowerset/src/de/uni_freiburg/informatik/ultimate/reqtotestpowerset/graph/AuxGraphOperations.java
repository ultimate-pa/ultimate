package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

public class AuxGraphOperations {



	public static GuardGraph makePowerSetAutomaton(List<GuardGraph> automata, Script mScript) {
		// take first automaton from list
		GuardGraph prodAut = automata.get(0);
		// remove first automaton from list
		automata.remove(0);
		// iterate over the remaining automata
		for (GuardGraph auto : automata) {
			// create cut automaton between taken automaton and one automaton from list
			GuardGraph prodOfTwo = makeProductOfTwoAutomata(prodAut, auto, mScript);
			// resulted product of 2 automata is now the left term for the next round of product
			// TODO maybe need to copy/clone the prodOfTwo to prodAut... need to research this further
			prodAut = prodOfTwo;
		}
		return prodAut;
	}

	private boolean addNewTransition(Script script, GuardGraph node1, GuardGraph node2, Term t1, Term t2) {
		node1.connectOutgoing(node2, SmtUtils.and(script, t1, t2));
		return true;
	}

	/* a helper modulo operation to find 
	 * A = {0...n}, B = {0...m}
	 * given i from A and j from B
	 * nodeId = i * |B| + j
	 */
	private static int findTheNode(int idNode1, int idNode2, int sizeOfB) {
		return idNode1 * sizeOfB + idNode2;
	}
	
	private static GuardGraph makeProductOfTwoAutomata(GuardGraph auto1, GuardGraph auto2, Script mScript) {

		final List<GuardGraph> auto1Nodes = auto1.getOutgoingNodes();
		final List<GuardGraph> auto2Nodes = auto2.getOutgoingNodes();

		final int nrOfNodes = auto1Nodes.size() * auto2Nodes.size();
		
		final List<GuardGraph> newStates = new ArrayList<>();
		for (int i = 0; i < nrOfNodes; i++) {
			newStates.add(new GuardGraph(i));
		}
		/*
		 *  let G1 = (V1, R1), let G2 = (V2, R2)
		 *  (v, X, v') element G1
		 *  (w, Y, w') element G2
		 *  (v, X, v') x (w, Y, w') = (vw, X and Y, v'w')
		 * 
		 *  Startnode = vw   also (findTheNode(v, w, sizeOf(V2))
		 *  Endnode = v'w'   also (findTheNode(v', w', sizeOf(V2))
		 */
		Term conjTerm;
		Term X;
		Term Y;
		for (GuardGraph v : auto1Nodes) {
			for(GuardGraph vl : auto1Nodes) {
				if (v.getOutgoingEdgeLabel(vl) != null) {
					// take the term, now we have (v, X, v')
					X = v.getOutgoingEdgeLabel(vl);
					// TODO this does not work... throws exception array index out of range
					/* possible optimization, skip edges with the label false
					if (SmtUtils.isFalse(X)) {
						continue;
					}
					*/
					
					// now for the second term and tuple
					for (GuardGraph w : auto2Nodes) {
						for (GuardGraph wl : auto2Nodes) {
							if (!(w.getOutgoingEdgeLabel(wl) == null)) {
								// take the term, now we have (w, Y, w')
								Y = w.getOutgoingEdgeLabel(wl);
								// TODO test this
								// possible optimization, skip edges with the label false
								/*if (SmtUtils.isFalse(Y)) {
									continue;
								}*/
								int fromIndex = findTheNode(v.getLabel(), w.getLabel(), auto2Nodes.size());
								int toIndex = findTheNode(vl.getLabel(), wl.getLabel(), auto2Nodes.size());
								conjTerm = SmtUtils.and(mScript, X, Y);
								
								newStates.get(fromIndex).connectOutgoing(newStates.get(toIndex), conjTerm);
							} else {
								// TODO that the edge is null
							}
						}
					}
				} else {
					// TODO warn that the edge is null
				}
			}
		}
		return newStates.get(0);
	}
}
