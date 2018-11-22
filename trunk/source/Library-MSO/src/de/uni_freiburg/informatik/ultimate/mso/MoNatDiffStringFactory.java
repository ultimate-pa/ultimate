/**
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;

/**
 * Not what we were looking for.
 *  
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MoNatDiffStringFactory implements IIntersectionStateFactory<String> {
	
	BigInteger mCounter;
	
	public MoNatDiffStringFactory() {
		mCounter = BigInteger.ZERO;
	}
	
	@Override
	public String createEmptyStackState() {
		return "€";
	}
	
	@Override
	public String intersection(final String state1, final String state2) {
		final String str = mCounter.toString();
		mCounter.add(BigInteger.ONE);
				
		return str;
	}
}