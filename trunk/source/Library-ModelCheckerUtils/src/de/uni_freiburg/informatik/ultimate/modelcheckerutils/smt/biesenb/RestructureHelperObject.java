package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class RestructureHelperObject {

	private static int sSerial = 0;

	private final int mSerialNumber;
	private final Map<Term, Term> mWitness;
	private final IPredicate mPredicate;

	public RestructureHelperObject(final int serialNumber, final Map<Term, Term> witnesses,
			final IPredicate predicate) {
		mSerialNumber = serialNumber;
		mWitness = witnesses;
		mPredicate = predicate;
	}

	public RestructureHelperObject(final Map<Term, Term> witnesses, final IPredicate predicate) {
		mSerialNumber = sSerial++;
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
