package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class Witness {
	
	private Map<Term, Term> mWitness;
	private int mSerialNumber;

	public Witness(int serialNumber, Map<Term, Term> witness) {
		mWitness = witness;
		mSerialNumber = serialNumber;
	}
	
	public Map<Term, Term> getWitness(){
		return mWitness;
	}
	
	public int getSerialNumber(){
		return mSerialNumber;
	}
}
