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
import java.util.BitSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.NavigableMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;


/**
 * Class representing a variable in a linear combination. This might either be
 * a slack variable or a real variable as introduced by the problem. For slack
 * variables we use the object name to refer to the corresponding linear term.
 *
 * Natural order depends on the order of creation of variables. That is every
 * variable is ordered according to their creation time. Ordering on the
 * variables is one requirement to be able to prove termination of the
 * algorithm.
 *
 * Every variable knows all possible bound constraints referring to it. This
 * way, bound propagations can easily be implemented.
 *
 * @author Juergen Christ
 */
public class LinVar implements Comparable<LinVar> {
	/**
	 * Name of the variable.  This is either a SharedTermOld for initially
	 * non-basic variables or a LinTerm for initially basic variables.
	 */
	Object mName;

	LiteralReason mUpperLiteral;
	LiteralReason mLowerLiteral;

	/** Current upper bound and its reason. null if no upper bound. */
	LAReason mUpper;
	/** Current lower bound and its reason. null if no lower bound. */
	LAReason mLower;
	/** Current value. */
	private ExactInfinitesimalNumber mCurval;
	// Is value required to be integer?
	boolean mIsInt;
	// List of all bounds on this variable
	NavigableMap<InfinitesimalNumber, BoundConstraint> mConstraints =
		new TreeMap<>();
	// List of all equalities known for this variable
	NavigableMap<InfinitesimalNumber, LAEquality> mEqualities =
		new TreeMap<>();

	/**
	 * All disequalities asserted on this variable.
	 */
	Map<Rational,LAEquality> mDisequalities;
	// Is this variable currently basic? NOTE: THIS IS THE CURRENT STATUS
	boolean mBasic;
	// Number to sort this variable in the sparse matrix
	final int mMatrixpos;

	LinVar[] mCachedRowVars;
	Rational[] mCachedRowCoeffs;

	int mAssertionstacklevel;

	ExactInfinitesimalNumber mExactVal = null;

	/// --- Construction ---
	/**
	 * Constructs a dummy linear variable.
	 */
	private LinVar() {
		mName = "Dummy";
		mMatrixpos = Integer.MAX_VALUE;
	}
	/**
	 * Constructor for a variable.
	 * @param name  Name of the variable (Needed for printout).
	 * @param isint Is the variable required to be integral valued?
	 * @param assertionstacklevel The number of pushes succeeded before this
	 * 							  variable has been created.
	 * @param num The count for this variable.
	 */
	public LinVar(final Object name,final boolean isint, final int assertionstacklevel, final int num) {
		mName = name;
		mCurval = ExactInfinitesimalNumber.ZERO;
		mIsInt = isint;
		mBasic = false;
		mMatrixpos = num;

		mAssertionstacklevel = assertionstacklevel;
	}
	/**
	 * Get the upper bound.
	 * @return Upper bound.
	 */
	public final InfinitesimalNumber getUpperBound() {
		return mUpperLiteral == null ? InfinitesimalNumber.POSITIVE_INFINITY : mUpperLiteral.getBound();
	}
	/**
	 * Get the lower bound.
	 * @return Lower bound.
	 */
	public final InfinitesimalNumber getLowerBound() {
		return mLowerLiteral == null ? InfinitesimalNumber.NEGATIVE_INFINITY : mLowerLiteral.getBound();
	}

	public final InfinitesimalNumber getTightUpperBound() {
		return mUpper == null ? InfinitesimalNumber.POSITIVE_INFINITY : mUpper.getBound();
	}

	public final InfinitesimalNumber getTightLowerBound() {
		return mLower == null ? InfinitesimalNumber.NEGATIVE_INFINITY : mLower.getBound();
	}
	public InfinitesimalNumber getExactUpperBound() {
		return mUpper == null ? InfinitesimalNumber.POSITIVE_INFINITY
			: mUpper.getExactBound();
	}
	public InfinitesimalNumber getExactLowerBound() {
		return mLower == null ? InfinitesimalNumber.NEGATIVE_INFINITY
			: mLower.getExactBound();
	}
	/**
	 * Check whether the upper bound is set.
	 * @return <code>true</code> iff upper bound is finite.
	 */
	public final boolean hasTightUpperBound() {
		return mUpper != null;
	}
	/**
	 * Check whether the lower bound is set.
	 * @return <code>true</code> iff lower bound is finite.
	 */
	public final boolean hasTightLowerBound() {
		return mLower != null;
	}
	/// --- Name stuff ---
	@Override
	public String toString() {
		return mName.toString();
	}
	/// --- Initially basic testing ---
	/**
	 * Check whether this variable is initially basic.
	 * @return <code>true</code> iff this variable corresponds to a linear term
	 */
	public boolean isInitiallyBasic() {
		return mName instanceof LinTerm;
	}

	@Override
	public int hashCode() {
		return mMatrixpos;
	}

	@Override
	public final int compareTo(final LinVar o) {
		return mMatrixpos - o.mMatrixpos;
	}
	/**
	 * Check whether this variable has a value outside its bounds.
	 * @return <code>false</code> iff <code>mlbound<=mcurval<=mubound</code>.
	 */
	public boolean outOfBounds() {
		if (mUpperLiteral != null) {
			if (mCurval.compareTo(mUpperLiteral.getBound()) > 0) {
				return true;
			}
		}
		if (mLowerLiteral != null) {
			if (mCurval.compareTo(mLowerLiteral.getExactBound()) < 0) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Dummy linear variable marking end of a non-basic chain.
	 */
	final static LinVar DUMMY_LINVAR = new LinVar();

	void addDiseq(final LAEquality ea) {
		if (mDisequalities == null) {
			mDisequalities = new HashMap<>();
		}
		mDisequalities.put(ea.getBound(), ea);
	}
	void removeDiseq(final LAEquality ea) {
		// mdisequalities can be null, if the literal was not set, because
		// it already produced a conflict in another theory.
		if (mDisequalities != null) {
			mDisequalities.remove(ea.getBound());
		}
	}
	LAEquality getDiseq(final Rational bound) {
		if (mDisequalities != null) {
			return mDisequalities.get(bound);
		}
		return null;
	}
	public void addEquality(final LAEquality ea) {
		mEqualities.put(new InfinitesimalNumber(ea.getBound(), 0), ea);
	}
	boolean unconstrained() {
		return mConstraints.isEmpty() && mEqualities.isEmpty();
	}
	boolean isCurrentlyUnconstrained() {
		return mLower == null && mUpper == null;
	}
	public boolean isInt() {
		return mIsInt;
	}
	public InfinitesimalNumber getEpsilon() {
		return mIsInt ? InfinitesimalNumber.ONE : InfinitesimalNumber.EPSILON;
	}

	/**
	 * Get the linear term from which this basic linvar was created.
	 * @throws ClassCastException if this is not an initially basic variable.
	 * @return the LinTerm.
	 */
	public Map<LinVar,BigInteger> getLinTerm() {
		return (LinTerm) mName;
	}

	/**
	 * Get the term which this non-basic linvar represents.
	 *
	 * @throws ClassCastException
	 *             if this is not an initially non-basic variable.
	 * @return the term.
	 */
	public Term getTerm() {
		return (Term) mName;
	}

	public boolean checkCoeffChain(final LinArSolve solver) {
		if (!mBasic) {
			return true;
		}
		final MutableAffineTerm mat = new MutableAffineTerm();
		final BigInteger headCoeff = solver.mTableaux.get(mMatrixpos).getRawCoeff(0);
		mat.add(Rational.valueOf(headCoeff, BigInteger.ONE), this);
		for (final MatrixEntry entry : getTableauxRow(solver)) {
			assert entry.getRow() == this;
			assert !entry.getColumn().mBasic;
			assert solver.mDependentRows.get(entry.getColumn().mMatrixpos).get(mMatrixpos);
			mat.add(Rational.valueOf(entry.getCoeff(), BigInteger.ONE), entry.getColumn());
		}
		assert mat.isConstant() && mat.getConstant().equals(InfinitesimalNumber.ZERO);
		return true;
	}

	public boolean isFixed() {
		return mUpper != null && mLower != null
			&& mUpper.getBound().equals(mLower.getBound());
	}

	public LAEquality getEquality(final InfinitesimalNumber bound) {
		return mEqualities.get(bound);
	}

	public final ExactInfinitesimalNumber getValue() {
		return mCurval;
	}

	public final void setValue(final ExactInfinitesimalNumber value) {
		mCurval = value;
	}

	public final void addValue(final ExactInfinitesimalNumber value) {
		mCurval = mCurval.add(value);
	}

	private boolean checkReasonChain(LAReason reason, LiteralReason litreason) {
		while (reason != null) {
			if (reason instanceof LiteralReason) {
				assert reason == litreason;
				litreason = litreason.getOldLiteralReason();
			}
			reason = reason.getOldReason();
		}
		assert litreason == null;
		return true;
	}

	public boolean checkReasonChains() {
		return checkReasonChain(mUpper, mUpperLiteral)
				&& checkReasonChain(mLower, mLowerLiteral);
	}

	public Iterable<MatrixEntry> getTableauxRow(final LinArSolve solver) {
		assert mBasic;
		final TableauxRow row = solver.mTableaux.get(mMatrixpos);
		assert row != null;
		return new Iterable<MatrixEntry>() {

			@Override
			public Iterator<MatrixEntry> iterator() {
				return new Iterator<MatrixEntry>() {
					private int pos = 1;

					@Override
					public boolean hasNext() {
						return pos < row.size();
					}

					@Override
					public MatrixEntry next() {
						return new MatrixEntry(solver, row, pos++);
					}
				};
			}
		};
	}

	public Iterable<MatrixEntry> getTableauxColumn(final LinArSolve solver) {
		assert !mBasic;
		final BitSet dependentRows = solver.mDependentRows.get(mMatrixpos);
		return new Iterable<MatrixEntry>() {

			@Override
			public Iterator<MatrixEntry> iterator() {
				return new Iterator<MatrixEntry>() {
					private int mRowIdx = dependentRows.nextSetBit(0);

					@Override
					public boolean hasNext() {
						return mRowIdx != -1;
					}

					@Override
					public MatrixEntry next() {
						final TableauxRow row = solver.mTableaux.get(mRowIdx);
						final MatrixEntry result = new MatrixEntry(solver, row, row.findRawIndex(mMatrixpos));
						assert result.getColumn() == LinVar.this;
						mRowIdx = dependentRows.nextSetBit(mRowIdx + 1);
						return result;
					}
				};
			}
		};
	}
}
