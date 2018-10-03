package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class RestructureHelperObject {
	
	final private int mSerialNumber;
	final private Map<Term, Term> mWitness;
	final private IPredicate mPredicate;

	public RestructureHelperObject(int serialNumber, Map<Term, Term> witnesses, IPredicate predicate) {
		mSerialNumber = serialNumber;
		mWitness = witnesses;
		mPredicate = predicate;
	}
	
	public int getSerialNumber(){
		return mSerialNumber;
	}
	
	public Map<Term, Term> getWitness(){
		return mWitness;
	}
	
	public IPredicate getPredicatet(){
		return mPredicate;
	}
}
