/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.math.BigInteger;

/**
 * This represents an entry in our sparse matrix.
 *
 * @author Jochen Hoenicke
 */
public class MatrixEntry {
	private final LinArSolve mSolver;
	private final TableauxRow mRow;
	private final int mPosition;

	public MatrixEntry(final LinArSolve solver, final TableauxRow row, final int pos) {
		mSolver = solver;
		mRow = row;
		mPosition = pos;
	}

	public LinVar getColumn() {
		return mSolver.mLinvars.get(mRow.getRawIndex(mPosition));
	}

	public LinVar getRow() {
		return mSolver.mLinvars.get(mRow.getRawIndex(0));
	}

	public BigInteger getCoeff() {
		return mRow.getRawCoeff(mPosition);
	}

	public BigInteger getHeadCoeff() {
		assert mPosition != 0;
		return mRow.getRawCoeff(0);
	}

	@Override
	public String toString() {
		if (mPosition == 0) {
			return mRow.toString();
		}
		return "[" + getRow() + "/" + getColumn() + "]->" + getCoeff();
	}
}
