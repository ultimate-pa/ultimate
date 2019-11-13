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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;

/**
 * Code to find a function application for a given function symbol that has the given term as argument at the given
 * position. Executing this code will install a trigger in the CClosure such that all new function applications with
 * these properties are noticed. The remaining code can be executed for each new function application.
 * 
 * @author Tanja Schindler
 */
public class ReverseCode implements ICode {

	private final EMatching mEMatching;

	private final int mArgRegIndex;
	private final FunctionSymbol mFunc;
	private final int mArgPos;
	private final int mOutRegIndex;
	private final ICode mRemainingCode;

	public ReverseCode(final EMatching eMatching, final int argRegIndex, final FunctionSymbol func, final int argPos,
			final int outRegIndex, final ICode remainingCode) {
		mEMatching = eMatching;
		mArgRegIndex = argRegIndex;
		mFunc = func;
		mArgPos = argPos;
		mOutRegIndex = outRegIndex;
		mRemainingCode = remainingCode;
	}

	@Override
	public void execute(final CCTerm[] register, final int decisionLevel) {
		final CCTerm arg = register[mArgRegIndex];
		mEMatching.installReverseTrigger(mFunc, arg, mArgPos, mOutRegIndex, mRemainingCode, register, decisionLevel);
		final List<CCTerm> funcApps =
				mEMatching.getQuantTheory().getCClosure().getAllFuncAppsForArg(mFunc, arg, mArgPos);
		for (final CCTerm cand : funcApps) {
			final CCTerm[] updatedReg = Arrays.copyOf(register, register.length);
			updatedReg[mOutRegIndex] = cand;
			assert cand instanceof CCAppTerm;
			CCAppTerm partialApp = (CCAppTerm) cand;
			for (int i = 0; i < mFunc.getParameterSorts().length - mArgPos - 1; i++) {
				partialApp = (CCAppTerm) ((CCAppTerm) partialApp).getFunc();
			}
			final CCTerm candArg = partialApp.getArg();
			final int termDecisionLevel = mEMatching.getQuantTheory().getCClosure().getDecideLevelForPath(arg, candArg);

			mEMatching.addCode(mRemainingCode, updatedReg,
					termDecisionLevel > decisionLevel ? termDecisionLevel : decisionLevel);
		}
	}

	@Override
	public String toString() {
		return "reverse(" + mFunc + ", " + mArgPos + ", r" + mArgRegIndex + ", r" + mOutRegIndex + ",\n"
				+ mRemainingCode.toString() + ")";
	}

}
