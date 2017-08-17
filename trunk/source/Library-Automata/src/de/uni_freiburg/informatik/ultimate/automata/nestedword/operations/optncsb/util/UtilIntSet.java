package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.Options;

public class UtilIntSet {
	
	private UtilIntSet() {
		
	}
	
	public static String getSetType() {
		String setType = null;
		switch(Options.setChoice) {
//		case 1:
//			setType = "SparseBitSet";
//			break;
//		case 2:
//			setType = "TIntSet";
//			break;
		case 1:
			setType = "TreeSet";
			break;
		case 2:
			setType = "HashSet";
			break;
		default:
			setType = "BitSet";
			break;
		}
		return setType;
	}
	
	public static IntSet newIntSet() {
		IntSet set = null;
		switch(Options.setChoice) {
//		case 1:
//			set = new IntSetSparseBits();
//			break;
//		case 2:
//			set = new IntSetTIntSet();
//			break;
		case 1:
			set = new IntSetTreeSet();
			break;
		case 2:
			set = new IntSetHashSet();
			break;
		default:
			set = new IntSetBits();
			break;
		}
		return set;
	}

}
