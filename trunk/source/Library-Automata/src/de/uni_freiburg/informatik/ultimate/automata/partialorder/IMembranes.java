package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Set;

/**
 * interface for membranes used in the dynamic partial order reduction algorithm
 *
 * @author Tilo Heep
 *
 * @param <STATE>
 *            The type of states in which the set of letters is a membrane
 * @param <LETTER>
 *            The type of letters which are in the membrane set
 */
public interface IMembranes<LETTER, STATE> {

	/**
	 *
	 * @param s:
	 *            state in which the membrane set should be computed
	 * @return a set of enabled letters being a membrane in state s
	 */
	Set<LETTER> getMembraneSet(STATE s);
}