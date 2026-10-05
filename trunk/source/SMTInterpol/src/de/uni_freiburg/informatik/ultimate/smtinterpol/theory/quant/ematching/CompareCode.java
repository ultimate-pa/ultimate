/*
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCParameter;

/**
 * Code to compare two values. If the values are equal, the remaining code can be executed. If they are not yet equal,
 * executing the Compare code will install a trigger in the CClosure.
 *
 * @author Tanja Schindler
 */
public class CompareCode implements ICode {

	private final EMatching mEMatching;
	private final int mFirstRegIndex, mSecondRegIndex;
	private final ICode mRemainingCode;

	public CompareCode(final EMatching eMatching, final int firstRegIndex, final int secondRegIndex,
			final ICode remainingCode) {
		mEMatching = eMatching;
		mFirstRegIndex = firstRegIndex;
		mSecondRegIndex = secondRegIndex;
		mRemainingCode = remainingCode;
	}

	@Override
	public void execute(final CCParameter[] register, final int decisionLevel) {
		final CCParameter firstTerm = register[mFirstRegIndex];
		final CCParameter secondTerm = register[mSecondRegIndex];
		if (firstTerm.sameValueAs(secondTerm)) {
			final int eqDecisionLevel = mEMatching.getQuantTheory().getCClosure()
					.getDecideLevelForPath(firstTerm.getCCTerm(), secondTerm.getCCTerm());
			mEMatching.addCode(mRemainingCode, register,
					eqDecisionLevel > decisionLevel ? eqDecisionLevel : decisionLevel);
		} else if (firstTerm.getCCTerm() != secondTerm.getCCTerm()) {
			mEMatching.installCompareTrigger(firstTerm, secondTerm, mRemainingCode, register, decisionLevel);
		}
		// else: the same base term at two different offsets; the values can never become equal.
	}

	@Override
	public String toString() {
		return "compare(r" + mFirstRegIndex + ", r" + mSecondRegIndex + ",\n" + mRemainingCode.toString() + ")";
	}
}
