package local.stalin.SMTInterface.z3interpol;

import java.util.Arrays;

import local.stalin.logic.Formula;

public class Interpolants {
	
	/// Flags describing source of the derivation
	public final static int DERIVATION_UNKNOWN = 0;
	public final static int DERIVATION_A = 1;
	public final static int DERIVATION_B = 2;
	public final static int DERIVATION_MIXED = DERIVATION_A | DERIVATION_B;// or simply 3...
	private Formula[] mips;
	private int[] msources;
	public Interpolants(int num) {
		mips = new Formula[num];
		msources = new int[num];
		// TODO: Check whether this array needs to be initialized in advance.
		Arrays.fill(msources,DERIVATION_UNKNOWN);
	}
	public Interpolants(Formula[] ips) {
		mips = ips;
		msources = new int[ips.length];
		// TODO: Check whether this array needs to be initialized in advance.
		Arrays.fill(msources,DERIVATION_UNKNOWN);
	}
	public void setInterpolant(int num,Formula ip) {
		mips[num] = ip;
	}
	public Formula getInterpolant(int num) {
		return mips[num];
	}
	public void setSource(int num,int source) {
		msources[num] = source;
	}
	public int getSource(int num) {
		return msources[num];
	}
	public int getSize() {
		return mips.length;
	}
	public Formula[] getInterpolants() {
		return mips;
	}
	public static Interpolants createInterpolants(Formula f,int num) {
		Interpolants res = new Interpolants(num);
		Arrays.fill(res.mips,f);
		return res;
	}
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Interpolants: ").append(Arrays.toString(mips)).append(" with sources ").append(Arrays.toString(msources));
		return sb.toString();
	}
	public int getSourceChangeIdx() {
		assert(msources[0] == DERIVATION_B);
		int i = 0;
		while( i < msources.length && msources[i] != DERIVATION_A )
			++i;
		return i;
	}
}
