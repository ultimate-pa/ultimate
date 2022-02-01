/*
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.logic;

import java.util.ArrayDeque;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * Represents a match term in SMTLIB 2.  This class represents the
 * SMTLIB 2 construct
 * <pre>
 * (match t (((c_1 v_11.. v1m) t_1) ... ((c_n v_n1.. vnm) t_m)))
 * </pre>
 *
 * @author Jochen Hoenicke
 */
public class MatchTerm extends Term {
	private final Term mDataTerm;
	private final TermVariable[][] mVariables;
	private final Term mCases[];
	private final DataType.Constructor[] mConstructors;

	MatchTerm(final int hash, final Term dataArg, final TermVariable[][] vars, final Term[] cases,
			final DataType.Constructor[] constructors) {
		super(hash);
		mDataTerm = dataArg;
		mVariables = vars;
		mCases = cases;
		mConstructors = constructors;
	}

	@Override
	public Sort getSort() {
		return mCases[0].getSort();
	}

	public Term getDataTerm() {
		return mDataTerm;
	}

	public DataType.Constructor[] getConstructors() {
		return mConstructors;
	}

	public TermVariable[][] getVariables() {
		return mVariables;
	}

	public Term[] getCases() {
		return mCases;
	}

	public static final int hashMatch(final Term dataArg, final TermVariable[][] vars, final Term[] cases) {
		return HashUtils.hashJenkins(dataArg.hashCode(), (Object[]) cases);
	}

	@Override
	public void toStringHelper(final ArrayDeque<Object> mTodo) {
		final DataType dataType = (DataType) mDataTerm.getSort().getRealSort().getSortSymbol();
		// Add subterm to stack.
		mTodo.addLast("))");
		for (int i = mCases.length - 1; i >= 0; i--) {
			mTodo.addLast(")");
			mTodo.addLast(mCases[i]);
			if (mConstructors[i] == null) {
				mTodo.addLast(" ");
				mTodo.addLast(mVariables[i][0]);
			} else if (mVariables[i].length > 0) {
				mTodo.addLast(") ");
				for (int j = mVariables[i].length - 1; j >= 0; j--) {
					mTodo.addLast(mVariables[i][j]);
					mTodo.addLast(" ");
				}
				mTodo.addLast(mConstructors[i].getName());
				mTodo.addLast("(");
			} else {
				mTodo.addLast(" ");
				mTodo.addLast(mConstructors[i].getName());
			}
			mTodo.addLast(i > 0 ? " (" : "(");
		}
		mTodo.addLast(" (");
		mTodo.addLast(mDataTerm);
		mTodo.addLast("(match ");
	}
}
