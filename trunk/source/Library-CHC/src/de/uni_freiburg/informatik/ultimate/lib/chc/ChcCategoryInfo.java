package de.uni_freiburg.informatik.ultimate.lib.chc;

import de.uni_freiburg.informatik.ultimate.logic.Logics;

public class ChcCategoryInfo {

	private Logics mConstraintLogic;

	private boolean mContainsNonLinearHornClauses;



	public ChcCategoryInfo(final Logics constraintLogic, final boolean containsNonLinearHornClauses) {
		super();
		mConstraintLogic = constraintLogic;
		mContainsNonLinearHornClauses = containsNonLinearHornClauses;
	}

	public Logics getConstraintLogic() {
		return mConstraintLogic;
	}

	public void setConstraintLogic(final Logics constraintLogic) {
		mConstraintLogic = constraintLogic;
	}

	public boolean containsNonLinearHornClauses() {
		return mContainsNonLinearHornClauses;
	}

	public void setContainsNonLinearHornClauses(final boolean containsNonLinearHornClauses) {
		mContainsNonLinearHornClauses = containsNonLinearHornClauses;
	}

}
