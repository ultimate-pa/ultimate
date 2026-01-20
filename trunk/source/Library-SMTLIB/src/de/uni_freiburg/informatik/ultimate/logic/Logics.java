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
package de.uni_freiburg.informatik.ultimate.logic;

/**
 * All logics configured in SMTLIB and some extensions supported by SMTInterpol.
 * @author Juergen Christ
 */
public class Logics {
	private final String mName;

	public static Logics CORE = valueOf("CORE");
	public static Logics ALL = valueOf("ALL");
	public static Logics HORN = valueOf("HORN");

	static class Features {
		/** flag for quantified logic. */
		static final int QU = (1 << 0);
		/** flag for uninterpreted functions. */
		static final int UF = (1 << 1);
		/** flag for array theory. */
		static final int AX = (1 << 2);
		/** flag for bit vector theory. */
		static final int BV = (1 << 3);
		/** flag for difference logic. */
		static final int DL = (1 << 4);
		/** flag for linear arithmetic. */
		static final int LA = (1 << 5);
		/** flag for non-linear arithmetic. */
		static final int NA = (1 << 6);
		/** flag for integer arithmetic. */
		static final int IA = (1 << 7);
		/** flag for real arithmetic. */
		static final int RA = (1 << 8);
		/** flag for floating point arithmetic. */
		static final int FP = (1 << 9);
		/** flag for datatypes. */
		static final int DT = (1 << 10);
		/** flag for string theory. */
		static final int S = (1 << 11);
	}

	private final int mFeatures;

	private Logics(final String name, final int features) {
		mName = name;
		mFeatures = features;
	}

	/**
	 * Create a logic with the given name
	 *
	 * @param logic the name of the logic
	 * @return the logic object.
	 * @throws IllegalArgumentException if the logic name is not supported.
	 */
	public static Logics valueOf(String logic) {
		int features;
		if (logic.equals("CORE")) {
			features = 0;
		} else if (logic.equals("ALL") || logic.equals("HORN")) {
			features = Features.QU + Features.NA + Features.IA + Features.RA + Features.BV + Features.UF + Features.AX
					+ Features.FP + Features.DT + Features.S;
		} else if (logic.matches("(QF_)?(A?(UF)?(BV)?(FP)?(DT)?S?([LN](I|R|IR)A|[IR]DL)?|AX)")) {
			features = logic.matches("QF_.*") ? 0 : Features.QU;
			if (logic.matches("(QF_)?A.*")) {
				features += Features.AX;
			}
			if (logic.matches(".*UF.*")) {
				features += Features.UF;
			}
			if (logic.matches(".*BV.*")) {
				features += Features.BV;
			}
			if (logic.matches(".*FP.*")) {
				features += Features.FP;
			}
			if (logic.matches(".*DT.*")) {
				features += Features.DT;
			}
			if (logic.matches(".*S.*")) {
				features += Features.S;
			}
			if (logic.matches(".*DL")) {
				features += Features.DL;
			}
			if (logic.matches(".*L[IR]*A")) {
				features += Features.LA;
			}
			if (logic.matches(".*N[IR]*A")) {
				features += Features.NA;
			}
			if (logic.matches(".*I.*")) {
				features += Features.IA;
			}
			if (logic.matches(".*R.*")) {
				features += Features.RA;
			}
		} else {
			throw new IllegalArgumentException("Unknown logic " + logic);
		}
		return new Logics(logic, features);
	}

	@Override
	public String toString() {
		return mName;
	}

	public String getName() {
		return mName;
	}

	/**
	 * Get the features. Only used for testing.
	 *
	 * @return the raw features as integer bitmap.
	 */
	int getFeatures() {
		return mFeatures;
	}

	/**
	 * Is this logic mixed integer and real?
	 * @return <code>true</code> if and only if mixed arithmetic can be used in
	 *         this logic.
	 */
	public boolean isIRA() {
		return (mFeatures & (Features.IA + Features.RA))
				== (Features.IA + Features.RA);
	}
	/**
	 * Does this logic support uninterpreted functions and sorts?
	 * @return <code>true</code> if and only if the logic supports uninterpreted
	 *         functions and sorts.
	 */
	public boolean isUF() {
		return (mFeatures & Features.UF) != 0;
	}
	/**
	 * Does this logic support arrays?
	 * @return <code>true</code> if and only if this logic supports arrays.
	 */
	public boolean isArray() {
		return (mFeatures & Features.AX) != 0;
	}
	/**
	 * Does this logic support bit vectors?
	 * @return <code>true</code> if and only if this logic supports bit vectors.
	 */
	public boolean isBitVector() {
		return (mFeatures & Features.BV) != 0;
	}
	/**
	 * Does this logic support quantifiers?
	 * @return <code>true</code> if and only if quantified formulas can be build
	 *         in this logic.
	 */
	public boolean isQuantified() {
		return (mFeatures & Features.QU) != 0;
	}

	/**
	 * Does this logic support arithmetic operators?
	 * @return <code>true</code> if and only if this logic supports arithmetic
	 */
	public boolean isArithmetic() {
		return (mFeatures & (Features.NA + Features.LA + Features.DL)) != 0;
	}

	/**
	 * Does this logic support difference logic?
	 * @return <code>true</code> if and only if this logic support difference
	 * logic;
	 * it returns false for linear arithmetic and non-linear arithmetic logics.
	 */
	public boolean isDifferenceLogic() {
		return (mFeatures & Features.DL) != 0;
	}
	/**
	 * Is this logic restricted to linear arithmetic?
	 * @return <code>true</code> if and only if this logic is restricted to linear arithmetic.
	 */
	public boolean isLinearArithmetic() {
		return (mFeatures & (Features.LA | Features.DL)) != 0;
	}
	/**
	 * Does this logic support non-linear arithmetic?
	 * @return <code>true</code> if and only if this logic support non-linear
	 * logic.
	 */
	public boolean isNonLinearArithmetic() {
		return (mFeatures & Features.NA) != 0;
	}
	/**
	 * Does this logic have integers?
	 * @return <code>true</code> if and only if this logic has integers.
	 */
	public boolean hasIntegers() {
		return (mFeatures & Features.IA) != 0;
	}
	/**
	 * Does this logic have real numbers?
	 * @return <code>true</code> if and only if this logic has reals.
	 */
	public boolean hasReals() {
		return (mFeatures & Features.RA) != 0;
	}
	/**
	 * Does this logic support floating point arithmetic?
	 * @return <code>true</code> if and only if this logic supports floating
	 * point arithmetic.
	 */
	public boolean isFloatingPoint() {
		return (mFeatures & Features.FP) != 0;
	}
	/**
	 * Does this logic support datatypes?
	 * @return <code>true</code> if and only if this logic supports datatypes.
	 */
	public boolean isDatatype() {
		return (mFeatures & Features.DT) != 0;
	}
	/**
	 * Does this logic support strings?
	 * @return <code>true</code> if and only if this logic supports strings.
	 */
	public boolean isString() {
		return (mFeatures & Features.S) != 0;
	}
}
