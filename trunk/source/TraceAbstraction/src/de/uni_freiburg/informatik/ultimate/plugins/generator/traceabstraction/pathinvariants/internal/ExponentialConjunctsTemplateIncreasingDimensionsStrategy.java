package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class ExponentialConjunctsTemplateIncreasingDimensionsStrategy
		extends AbstractTemplateIncreasingDimensionsStrategy {

	public ExponentialConjunctsTemplateIncreasingDimensionsStrategy(int initialDisjuncts, int initialConjuncts,
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
			return new int[] {1, 4};
		} else if (round == 4) {
			return new int[] {1, 8};
		} else if (round == 5) {
			return new int[] {1, 16};
		} else if (round == 6) {
			return new int[] {1, 32};
		} else if (round == 7) {
			return new int[] {2, 2};
		} else if (round == 8) {
			return new int[] {2, 4};
		} else if (round == 9) {
			return new int[] {2, 8};
		} else if (round == 10) {
			return new int[] {2, 16};
		} else {
			return new int[] { mInitialDisjuncts + round * mDisjunctsPerRound,
					mInitialConjuncts + round * mConjunctsPerRound };
		}
	}

}
