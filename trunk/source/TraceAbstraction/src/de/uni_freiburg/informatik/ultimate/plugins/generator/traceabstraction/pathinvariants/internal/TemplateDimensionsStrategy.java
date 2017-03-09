package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * 
 * @author Betim Musa <musab@informatik.uni-freiburg.de>
 *
 */
public class TemplateDimensionsStrategy {
	
	
	private final int mInitialDisjuncts;
	private final int mDisjunctsPerRound;
	private final int mInitialConjuncts;
	private final int mConjunctsPerRound;
	
	public TemplateDimensionsStrategy (final int initialDisjuncts, final int initialConjuncts,
			final int disjunctsPerRound, final int conjunctsPerRound) {
		mInitialDisjuncts = initialDisjuncts;
		mDisjunctsPerRound = disjunctsPerRound;
		mInitialConjuncts = initialConjuncts;
		mConjunctsPerRound = conjunctsPerRound;
		
	}
	
	

	public int[] getDimensions(IcfgLocation location, int round) {
		if (round == 1) {
			return new int[] {mInitialDisjuncts, mInitialConjuncts};
		} else if (round == 2) {
			return new int[] {mInitialDisjuncts, mInitialConjuncts + mConjunctsPerRound};
		} else if (round == 3) {
			return new int[] {mInitialDisjuncts + mDisjunctsPerRound, mInitialConjuncts + mConjunctsPerRound};
		} else if (round == 4) {
			return new int[] {mInitialDisjuncts + mDisjunctsPerRound, mInitialConjuncts + 2 * mConjunctsPerRound};
		} else if (round == 5) {
			return new int[] {mInitialDisjuncts + 2 * mDisjunctsPerRound, mInitialConjuncts + mConjunctsPerRound};
		} else if (round == 6) {
			return new int[] {mInitialDisjuncts + 2 * mDisjunctsPerRound, mInitialConjuncts + 2 * mConjunctsPerRound};
		} else {
			return new int[] { mInitialDisjuncts + round * mDisjunctsPerRound,
					mInitialConjuncts + round * mConjunctsPerRound };
		}
	}
	
	public int getInitialDisjuncts() {
		return mInitialDisjuncts;
	}
	
	public int getInitialConjuncts () {
		return mInitialConjuncts;
	}

}
