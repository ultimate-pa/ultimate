package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * 
 * @author Betim Musa <musab@informatik.uni-freiburg.de>
 *
 */
public class ConservativeTemplateIncreasingDimensionsStrategy extends AbstractTemplateIncreasingDimensionsStrategy {

	public ConservativeTemplateIncreasingDimensionsStrategy(int initialDisjuncts, int initialConjuncts,
			int disjunctsPerRound, int conjunctsPerRound) {
		super(initialDisjuncts, initialConjuncts, disjunctsPerRound, conjunctsPerRound);
		
	}
	
	@Override
	public int[] getDimensions(IcfgLocation location, int round) {
		if (round == 1) {
			return new int[] {1, 1};
		} else if (round == 2) {
			return new int[] {1, 2};
		} else if (round == 3) {
			return new int[] {1, 3};
		} else if (round == 4) {
			return new int[] {2, 1};
		} else if (round == 5) {
			return new int[] {2, 2};
		} else if (round == 6) {
			return new int[] {2, 3};
		} else if (round == 7) {
			return new int[] {3, 1};
		} else if (round == 8) {
			return new int[] {3, 2};
		} else if (round == 9) {
			return new int[] {3, 3};
		} else if (round == 10) {
			return new int[] {3, 4};
		} else {
			return new int[] { mInitialDisjuncts + round * mDisjunctsPerRound,
					mInitialConjuncts + round * mConjunctsPerRound };
		}
	}

}
