package de.uni_freiburg.informatik.ultimate.automata.rabin;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <STATE>
 *            type of state
 */
public interface IRainbowStateFactory<STATE> extends IStateFactory<STATE> {

	/**
	 * Modifies state so that each value of color results in a unique coloredState being returned
	 *
	 * @param state
	 *            a unmodified state
	 * @param color
	 *            a color to be encoded
	 * @return a unique state for the input parameter pair
	 */
	STATE getColoredState(STATE state, byte color);
}
