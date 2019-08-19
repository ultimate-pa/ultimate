/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * Script that wraps an existing Script but has additional checks for the construction of Terms. Whenever a Term is
 * constructed we check if all params have the same Theory. This is useful to detect the common mistake that Terms are
 * combined that have been constructed using different Scripts. This is not a perfect solution, should be considered as
 * a workaround and used only for debugging.
 *
 * @author Matthias Heizmann
 */
public class ScriptWithTermConstructionChecks extends WrapperScript {

	public ScriptWithTermConstructionChecks(final Script script) {
		super(script);
	}

	@Override
	public Term term(final String funcname, final Term... params) {
		checkIfsomeParamUsesDifferentTheory(params);
		return mScript.term(funcname, params);
	}

	private void checkIfsomeParamUsesDifferentTheory(final Term[] params) {
		for (final Term param : params) {
			final Theory paramTheory = getTheory(param);
			if (paramTheory != getThisScriptsTheory()) {
				throw new IllegalArgumentException("Param was constructed with different Script: " + param);
			}
		}
	}

	private static Theory getTheory(final Term param) {
		return param.getSort().getTheory();
	}

	private Theory getThisScriptsTheory() {
		return SmtSortUtils.getBoolSort(mScript).getTheory();
	}

	@Override
	public Term term(final String funcname, final BigInteger[] indices, final Sort returnSort, final Term... params) {
		checkIfsomeParamUsesDifferentTheory(params);
		return mScript.term(funcname, indices, returnSort, params);
	}

	@Override
	public LBool checkSatAssuming(final Term... assumptions) {
		throw new UnsupportedOperationException("Introduced in SMTInterpol 2.1-324-ga0525a0, not yet supported");
	}

	@Override
	public Term[] getUnsatAssumptions() {
		throw new UnsupportedOperationException("Introduced in SMTInterpol 2.1-324-ga0525a0, not yet supported");
	}

	@Override
	public void resetAssertions() {
		throw new UnsupportedOperationException("Introduced in SMTInterpol 2.1-324-ga0525a0, not yet supported");
	}
}
