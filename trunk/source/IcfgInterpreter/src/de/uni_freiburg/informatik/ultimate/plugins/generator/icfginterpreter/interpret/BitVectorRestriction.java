package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.BitVector;

public class BitVectorRestriction extends Restriction<BitVector> {
	public BitVectorRestriction(final HashSet<BitVector> inequal, final BitVector less, final BitVector greater) {
		super(inequal, less, greater);
	}
}