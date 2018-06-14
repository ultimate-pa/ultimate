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
public enum Logics {
	CORE(0),// Pure Boolean logic
	ALL       (Features.QU + Features.NA + Features.IA + Features.RA +
			   Features.BV + Features.UF + Features.AX + Features.FP),
	HORN      (Features.QU + Features.NA + Features.IA + Features.RA +
			   Features.BV + Features.UF + Features.AX + Features.FP),
	QF_BV     (Features.BV),
	QF_FP     (Features.UF + Features.FP),
	QF_BVFP   (Features.UF + Features.BV + Features.FP),
	QF_IDL    (Features.DL + Features.IA),
	QF_RDL    (Features.DL + Features.RA),
	QF_LIA    (Features.LA + Features.IA),
	QF_LRA    (Features.LA + Features.RA),
	QF_LIRA   (Features.LA + Features.RA + Features.IA),
	QF_NIA    (Features.NA + Features.IA),
	QF_NRA    (Features.NA + Features.RA),
	QF_NIRA   (Features.NA + Features.RA + Features.IA),
	QF_UF     (Features.UF),
	QF_UFBV   (Features.UF + Features.BV),
	QF_UFIDL  (Features.UF + Features.DL + Features.IA),
	QF_UFLIA  (Features.UF + Features.LA + Features.IA),
	QF_UFLRA  (Features.UF + Features.LA + Features.RA),
	QF_UFLIRA (Features.UF + Features.LA + Features.IA + Features.RA),
	QF_UFNIA  (Features.UF + Features.NA + Features.IA),
	QF_UFNRA  (Features.UF + Features.NA + Features.RA),
	QF_AX     (Features.AX),
	QF_ABV    (Features.AX + Features.BV),
	QF_AUFBV  (Features.AX + Features.UF + Features.BV),
	QF_ALIA   (Features.AX + Features.LA + Features.IA),
	QF_AUFLIA (Features.AX + Features.UF + Features.LA + Features.IA),
	QF_AUFLIRA(Features.AX + Features.UF + Features.LA + Features.IA + Features.RA), //NOCHECKSTYLE

	BV        (Features.QU + Features.BV),
	FP        (Features.QU + Features.UF + Features.FP),
	BVFP      (Features.QU + Features.UF + Features.BV + Features.FP),
	LIA       (Features.QU + Features.LA + Features.IA),
	LRA       (Features.QU + Features.LA + Features.RA),
	NIA       (Features.QU + Features.NA + Features.IA),
	NRA       (Features.QU + Features.NA + Features.RA),
	UF        (Features.QU + Features.UF),
	UFBV      (Features.QU + Features.UF + Features.BV),
	UFIDL     (Features.QU + Features.UF + Features.DL + Features.IA),
	UFLIA     (Features.QU + Features.UF + Features.LA + Features.IA),
	UFLRA     (Features.QU + Features.LA + Features.RA),
	UFNIA     (Features.QU + Features.NA + Features.IA),
	AUFBV     (Features.QU + Features.AX + Features.UF + Features.BV),
	ALIA      (Features.QU + Features.AX + Features.LA + Features.IA),
	AUFLIA    (Features.QU + Features.AX + Features.UF + Features.LA + Features.IA), //NOCHECKSTYLE
	AUFLIRA   (Features.QU + Features.AX + Features.UF + Features.LA + Features.IA + Features.RA), //NOCHECKSTYLE
	AUFNIRA   (Features.QU + Features.AX + Features.UF + Features.NA + Features.IA + Features.RA), //NOCHECKSTYLE

	; //NOCHECKSTYLE

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
	}

	private final int mFeatures;

	private Logics(final int features) {
		mFeatures = features;
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
	 * Does this logic support linear arithmetic?
	 * @return <code>true</code> if and only if this logic support difference
	 * logic; it returns false for nonlinear arithmetic logics.
	 */
	public boolean isLinearArithmetic() {
		return (mFeatures & Features.LA) != 0;
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
}
