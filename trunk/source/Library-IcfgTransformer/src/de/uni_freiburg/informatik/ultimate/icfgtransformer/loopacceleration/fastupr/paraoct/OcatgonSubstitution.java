package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

class OctagonSubstitution {
	private final TermVariable mVar;
	private final HashSet<OctagonSubstitutionTerm> mGreaterEqThan;
	private final HashSet<OctagonSubstitutionTerm> mLesserEqThan;

	protected OctagonSubstitution(TermVariable var) {
		mVar = var;
		mGreaterEqThan = new HashSet<>();
		mLesserEqThan = new HashSet<>();
	}

	void addSubstitution(OctTerm term) {
		if (term.getFirstVar().equals(mVar)) {
			addSubstitution(term, true);
		} else if (term.getSecondVar().equals(mVar)) {
			addSubstitution(term, false);
		}
	}

	void addSubstitution(OctTerm term, boolean first) {

		OctagonSubstitutionTerm subTerm;
		boolean greater = false;

		if (first) {
			if (term.isOneVar()) {
				subTerm = new OctagonSubstitutionTerm(term.getValue());
			} else {
				subTerm = new OctagonSubstitutionTerm(term.getValue(), term.getSecondVar(), term.isSecondNegative());
			}
			if (term.isFirstNegative()) {
				greater = true;
			}
		} else {
			subTerm = new OctagonSubstitutionTerm(term.getValue(), term.getFirstVar(), term.isFirstNegative());
			if (term.isSecondNegative()) {
				greater = true;
			}
		}

		addSubstitution(subTerm, greater);
	}

	void addSubstitution(OctagonSubstitutionTerm term, boolean greater) {
		if (greater) {
			mGreaterEqThan.add(term);
		} else {
			mLesserEqThan.add(term);
		}
	}

	HashSet<OctagonSubstitutionTerm> getGreaterSubsitutions() {
		return mGreaterEqThan;
	}

	HashSet<OctagonSubstitutionTerm> getLesserSubsitutions() {
		return mLesserEqThan;
	}

	@Override
	public String toString() {
		if (mGreaterEqThan.isEmpty() && mLesserEqThan.isEmpty()) {
			return " > Substitution for " + mVar.toString() + " empty. \n";
		}
		String result = " > Substitution for " + mVar.toString() + ":\n";
		result = result + ("Greater Equal Than: ");
		for (final OctagonSubstitutionTerm t : mGreaterEqThan) {
			result = result + (t.toString() + "; ");
		}
		result = result + ("\nLesser Equal Than: ");
		for (final OctagonSubstitutionTerm t : mLesserEqThan) {
			result = result + (t.toString() + "; ");
		}
		result = result + "\n";
		return result;
	}

}
