/**
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;

/**
 * Not what we were looking for.
 *  
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MoNatDiffStringFactory implements IIntersectionStateFactory<String> {
	
	@Override
	public String createEmptyStackState() {
		return "€";
	}
	
	@Override
	public String intersection(final String state1, final String state2) {
		final StringBuilder builder = new StringBuilder();
		builder.append(state1).append(state2);
				
		return builder.toString();
	}
}