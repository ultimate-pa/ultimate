package util;

import main.Options;

public class UtilIntSet {
	
	private UtilIntSet() {
		
	}
	
	public static String getSetType() {
		String setType = null;
		switch(Options.setChoice) {
		case 1:
			setType = "SparseBitSet";
			break;
		case 2:
			setType = "TIntSet";
			break;
		case 3:
			setType = "TreeSet";
			break;
		case 4:
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
		case 1:
			set = new IntSetSparseBits();
			break;
		case 2:
			set = new IntSetTIntSet();
			break;
		case 3:
			set = new IntSetTreeSet();
			break;
		case 4:
			set = new IntSetHashSet();
			break;
		default:
			set = new IntSetBits();
			break;
		}
		return set;
	}

}
