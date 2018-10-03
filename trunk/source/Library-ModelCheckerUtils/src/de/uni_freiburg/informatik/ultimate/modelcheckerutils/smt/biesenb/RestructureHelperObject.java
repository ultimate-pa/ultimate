package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class RestructureHelperObject {

	final private int mSerialNumber;
	final private Map<Term, Term> mWitness;
	final private IPredicate mPredicate;

	public RestructureHelperObject(final int serialNumber, final Map<Term, Term> witnesses,
			final IPredicate predicate) {
		mSerialNumber = serialNumber;
		mWitness = witnesses;
		mPredicate = predicate;
	}

	public int getSerialNumber() {
		return mSerialNumber;
	}

	public Map<Term, Term> getWitness() {
		return mWitness;
	}

	public IPredicate getPredicate() {
		return mPredicate;
	}
}
