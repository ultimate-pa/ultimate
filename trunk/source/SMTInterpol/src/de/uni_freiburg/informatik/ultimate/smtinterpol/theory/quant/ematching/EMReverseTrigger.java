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

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;

/**
 * A trigger to find new function applications. It has to be installed into the CClosure. Upon activation, the remaining
 * E-Matching code can be executed with the given register that is updated by the new term.
 *
 * @author Tanja Schindler
 */
public class EMReverseTrigger extends de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ReverseTrigger {

	private final EMatching mEMatching;
	private final ICode mRemainingCode;
	private final FunctionSymbol mFunc;
	private final int mArgPos;
	private final CCTerm mArg;
	private final CCTerm[] mRegister;
	private final int mOutRegIndex;
	private final int mDecisionLevel;

	public EMReverseTrigger(final EMatching eMatching, final ICode remainingCode, final FunctionSymbol func,
			final int argPos, final CCTerm arg, final CCTerm[] register, final int outRegIndex,
			final int decisionLevel) {
		mEMatching = eMatching;
		mRemainingCode = remainingCode;
		mFunc = func;
		mArgPos = argPos;
		mArg = arg;
		mRegister = register;
		mOutRegIndex = outRegIndex;
		mDecisionLevel = decisionLevel;
	}

	@Override
	public CCTerm getArgument() {
		return mArg;
	}

	@Override
	public int getArgPosition() {
		return mArgPos;
	}

	@Override
	public FunctionSymbol getFunctionSymbol() {
		return mFunc;
	}

	@Override
	public void activate(final CCAppTerm appTerm, final boolean isFresh) {
		final CCTerm[] updatedRegister = Arrays.copyOf(mRegister, mRegister.length);
		updatedRegister[mOutRegIndex] = appTerm;

		if (mArg != null) { // Reverse
			assert appTerm instanceof CCAppTerm;
			CCAppTerm partialApp = appTerm;
			for (int i = 0; i < mFunc.getParameterSorts().length - mArgPos - 1; i++) {
				partialApp = (CCAppTerm) partialApp.getFunc();
			}
			final CCTerm candArg = partialApp.getArg();
			final int termDecisionLevel = mEMatching.getQuantTheory().getCClosure()
					.getDecideLevelForPath(mArg, candArg);

			mEMatching.addCode(mRemainingCode, updatedRegister,
					termDecisionLevel > mDecisionLevel ? termDecisionLevel : mDecisionLevel);
		} else { // Find
			mEMatching.addCode(mRemainingCode, updatedRegister, mDecisionLevel);
		}
	}

}
