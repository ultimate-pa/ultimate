/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult.Equality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Check equality for pairs of terms with respect to a given context.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class IncrementalEqualityAnalyzer {
	
	private final ManagedScript mMgdScript;
	private final Term mContext;
	private boolean mContextIsAsserted;

	
	
	public IncrementalEqualityAnalyzer(final ManagedScript mgdScript, final Term context) {
		super();
		mMgdScript = mgdScript;
		mContext = context;
		mContextIsAsserted = false;
	}

	public void assertContext(final Term context) {
		assert !mContextIsAsserted : "must not assert context twice";
		mMgdScript.lock(this);
		mMgdScript.push(this, 1);
		mMgdScript.assertTerm(this, context);
		mContextIsAsserted = true;
	}
	
	
	/**
	 * This method does not use any efficient auxiliary methods to check
	 * equality. We presume that was done in advance.
	 */
	public Equality checkEquality(final Term lhs, final Term rhs) {
		if (!mContextIsAsserted) {
			assertContext(mContext);
		}
		final Term eq = mMgdScript.term(this, "=", lhs, rhs);
		mMgdScript.push(this, 1);
		mMgdScript.assertTerm(this, eq);
		final LBool satWithEq = mMgdScript.checkSat(this);
		mMgdScript.pop(this, 1);
		if (satWithEq == LBool.UNSAT) {
			return Equality.NOT_EQUAL;
		} else {
			final Term neq = mMgdScript.term(this, "not", eq);
			mMgdScript.push(this, 1);
			mMgdScript.assertTerm(this, neq);
			final LBool satWithNeq = mMgdScript.checkSat(this);
			mMgdScript.pop(this, 1);
			if (satWithNeq == LBool.UNSAT) {
				return Equality.NOT_EQUAL;
			} else {
				return Equality.UNKNOWN;
			}
		}
	}
	
	
	public void unlockSolver() {
		mMgdScript.pop(this, 1);
		mMgdScript.unlock(this);
	}
}

