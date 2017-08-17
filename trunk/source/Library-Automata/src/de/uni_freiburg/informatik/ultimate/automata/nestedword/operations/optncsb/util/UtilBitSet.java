package util;

import java.util.BitSet;

public class UtilBitSet {
	
	private UtilBitSet() {
		
	}
	
	// hope will faster
	public static boolean subsetOf(final BitSet A, final BitSet B) {
		
		if(A.cardinality() > B.cardinality()) return false;
		BitSet AP = (BitSet) A.clone();
		AP.andNot(B);
		if(AP.isEmpty()) return true;
		return false;
//		for(int n = A.nextSetBit(0); n >= 0; n = A.nextSetBit(n + 1)) {
//			if(n >= B.size()) return false;
//			if(! B.get(n)) return false;
//		}
//		return true;
	}
	
	public static boolean contentEq(final BitSet A, final BitSet B) {
		if(A.cardinality() != B.cardinality()) return false;
		int i = A.nextSetBit(0), j = B.nextSetBit(0);
		while(i >= 0 || j >= 0) {
			if(i != j) return false;
			i = A.nextSetBit(i + 1);
			j = B.nextSetBit(j + 1);
		}

		return true;
	}
	
	public static BitSet subtract(final BitSet A, final BitSet B) {
		
		BitSet bits = (BitSet) A.clone();
		bits.andNot(B);
//		for(int n = A.nextSetBit(0); n >= 0; n = A.nextSetBit(n + 1)) {
//			if(n >= B.size()) {
//				subBits.set(n);
//			}
//			// only set when n is not set in B
//			if(! B.get(n)) {
//				subBits.set(n);
//			}
//		}

		return bits;
	}
	
	public static BitSet union(final BitSet A, final BitSet B) {
		
		BitSet bits = (BitSet) A.clone();
		bits.or(B);
//		int i = A.nextSetBit(0), j = B.nextSetBit(0);
//		while(i >= 0 || j >= 0) {
//			if(i >= 0) {
//				bits.set(i);
//				i = A.nextSetBit(i + 1);
//			}
//			if(j >= 0) {
//				bits.set(j);
//				j = A.nextSetBit(j + 1);
//			}
//		}

		return bits;
	}
	
	public static BitSet intersect(final BitSet A, final BitSet B) {

		BitSet bits = (BitSet) A.clone();
		bits.and(B);
//		int i = A.nextSetBit(0), j = B.nextSetBit(0);
//		while(i >= 0 && j >= 0) {
//			if(i == j) {
//				bits.set(i);
//				i = A.nextSetBit(i + 1);
//				j = B.nextSetBit(j + 1);
//			}else if(i < j) i = A.nextSetBit(i + 1);
//			else j = B.nextSetBit(j + 1);
//		}

		return bits;
	}
	
	public static void main(String[] args) {
		BitSet A = new BitSet(17);
		BitSet B = new BitSet(19);
		BitSet C = new BitSet(15);
		
		for(int i = 1; i < 14; i += 2) {
			A.set(i);
			B.set(i);
			C.set(i);
		}
		
		System.out.println("A: " + A);
		System.out.println("B: " + B);
		System.out.println("C: " + C);
		
		System.out.println(UtilBitSet.contentEq(A, B));
		System.out.println(UtilBitSet.contentEq(C, A));
		
		B.set(15);
		
		System.out.println(UtilBitSet.subsetOf(A, B));
		System.out.println(UtilBitSet.subsetOf(B, A));
		System.out.println(UtilBitSet.subsetOf(B, C));
		System.out.println(UtilBitSet.subsetOf(C, B));
		
		System.out.println(UtilBitSet.subtract(B, C));
		System.out.println(UtilBitSet.subtract(C, B));
		
		System.out.println(UtilBitSet.intersect(C, B));
	}

}
