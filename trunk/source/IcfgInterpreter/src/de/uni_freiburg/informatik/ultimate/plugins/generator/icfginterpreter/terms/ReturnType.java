package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

public enum ReturnType {
	Boolean, Int, Array, BitVector;

	public static ReturnType getType(final Sort sort) {
		switch (sort.getName()) {
		case SMTLIBConstants.ARRAY:
			return ReturnType.Array;
		case SMTLIBConstants.BITVEC:
			return ReturnType.BitVector;
		case SMTLIBConstants.BOOL:
			return ReturnType.Boolean;
		case SMTLIBConstants.INT:
			return ReturnType.Int;
		}
		return null;
	}
}