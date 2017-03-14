package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * 
 * @author Betim Musa <musab@informatik.uni-freiburg.de>
 *
 */
public abstract class AbstractTemplateIncreasingDimensionsStrategy {
	protected final int mInitialDisjuncts;
	protected final int mDisjunctsPerRound;
	protected final int mInitialConjuncts;
	protected final int mConjunctsPerRound;
	
	public AbstractTemplateIncreasingDimensionsStrategy (final int initialDisjuncts, final int initialConjuncts,
			final int disjunctsPerRound, final int conjunctsPerRound) {
		mInitialDisjuncts = initialDisjuncts;
		mDisjunctsPerRound = disjunctsPerRound;
		mInitialConjuncts = initialConjuncts;
		mConjunctsPerRound = conjunctsPerRound;
		
	}
	
	

	public abstract int[] getDimensions(IcfgLocation location, int round); 

	
	public int getInitialDisjuncts() {
		return mInitialDisjuncts;
	}
	
	public int getInitialConjuncts () {
		return mInitialConjuncts;
	}

}
