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
			Features.BV + Features.UF + Features.AX + Features.FP + Features.DT + Features.S),
	HORN      (Features.QU + Features.NA + Features.IA + Features.RA +
			Features.BV + Features.UF + Features.AX + Features.FP + Features.DT + Features.S),
	QF_ABV    (Features.AX + Features.BV),
	QF_ABVFP  (Features.AX + Features.BV + Features.FP),
	QF_ABVFPLRA (Features.AX + Features.BV + Features.FP + Features.LA + Features.RA),
	QF_ALIA   (Features.AX + Features.LA + Features.IA),
	QF_ANIA   (Features.AX + Features.NA + Features.IA),
	QF_AUFBV  (Features.AX + Features.UF + Features.BV),
	QF_AUFBVFP (Features.AX + Features.UF + Features.BV + Features.FP),
	QF_AUFBVFPLRA (Features.AX + Features.UF + Features.BV + Features.FP + Features.LA + Features.RA),
	QF_AUFBVLIA (Features.AX + Features.UF + Features.BV + Features.LA + Features.IA),
	QF_AUFBVNIA (Features.AX + Features.UF + Features.BV + Features.NA + Features.IA),
	QF_AUFLIA (Features.AX + Features.UF + Features.LA + Features.IA),
	QF_AUFLIRA (Features.AX + Features.UF + Features.LA + Features.IA + Features.RA),
	QF_AUFNIA (Features.AX + Features.UF + Features.NA + Features.IA),
	QF_AUFNIRA (Features.AX + Features.UF + Features.NA + Features.IA + Features.RA),
	QF_AX     (Features.AX),
	QF_BV     (Features.BV),
	QF_BVFP   (Features.BV + Features.FP),
	QF_BVFPLRA (Features.BV + Features.FP + Features.LA + Features.RA),
	QF_BVLRA  (Features.BV + Features.LA + Features.RA),
	QF_DT     (Features.DT),
	QF_FP     (Features.FP),
	QF_FPLRA  (Features.FP + Features.LA + Features.RA),
	QF_IDL    (Features.DL + Features.IA),
	QF_LIA    (Features.LA + Features.IA),
	QF_LIRA   (Features.LA + Features.RA + Features.IA),
	QF_LRA    (Features.LA + Features.RA),
	QF_NIA    (Features.NA + Features.IA),
	QF_NIRA   (Features.NA + Features.RA + Features.IA),
	QF_NRA    (Features.NA + Features.RA),
	QF_RDL    (Features.DL + Features.RA),
	QF_S      (Features.S),
	QF_SLIA   (Features.S + Features.LA + Features.IA),
	QF_SNIA   (Features.S + Features.NA + Features.IA),
	QF_UF     (Features.UF),
	QF_UFBV   (Features.UF + Features.BV),
	QF_UFBVDT (Features.UF + Features.BV + Features.DT),
	QF_UFBVLIA (Features.UF + Features.BV + Features.LA + Features.IA),
	QF_UFDT   (Features.UF + Features.DT),
	QF_UFDTNIA (Features.UF + Features.DT + Features.NA + Features.IA),
	QF_UFDTLIA (Features.UF + Features.DT + Features.LA + Features.IA),
	QF_UFDTLIRA (Features.UF + Features.DT + Features.LA + Features.IA + Features.RA),
	QF_UFFP   (Features.UF + Features.FP),
	QF_UFFPDTLIRA (Features.UF + Features.FP + Features.DT + Features.LA + Features.IA + Features.RA),
	QF_UFFPDTNIRA (Features.UF + Features.FP + Features.DT + Features.NA + Features.IA + Features.RA),
	QF_UFIDL  (Features.UF + Features.DL + Features.IA),
	QF_UFLIA  (Features.UF + Features.LA + Features.IA),
	QF_UFLIRA (Features.UF + Features.LA + Features.IA + Features.RA),
	QF_UFLRA  (Features.UF + Features.LA + Features.RA),
	QF_UFNIA  (Features.UF + Features.NA + Features.IA),
	QF_UFNRA  (Features.UF + Features.NA + Features.RA),

	ABV       (Features.QU + Features.AX + Features.BV),
	ABVFP     (Features.QU + Features.AX + Features.BV + Features.FP),
	ABVFPLRA  (Features.QU + Features.AX + Features.BV + Features.FP + Features.LA + Features.RA),
	ALIA      (Features.QU + Features.AX + Features.LA + Features.IA),
	ANIA      (Features.QU + Features.AX + Features.NA + Features.IA),
	AUFBV     (Features.QU + Features.AX + Features.UF + Features.BV),
	AUFBVDTLIA (Features.QU + Features.AX + Features.UF + Features.BV + Features.DT + Features.LA + Features.IA),
	AUFBVDTNIA (Features.QU + Features.AX + Features.UF + Features.BV + Features.DT + Features.NA + Features.IA),
	AUFBVDTNIRA(Features.QU + Features.AX + Features.UF + Features.BV + Features.DT + Features.NA + Features.IA + Features.RA),
	AUFBVFP   (Features.QU + Features.AX + Features.UF + Features.BV + Features.FP),
	AUFDTLIA  (Features.QU + Features.AX + Features.UF + Features.DT + Features.LA + Features.IA),
	AUFDTNIA  (Features.QU + Features.AX + Features.UF + Features.DT + Features.NA + Features.IA),
	AUFDTLIRA (Features.QU + Features.AX + Features.UF + Features.DT + Features.LA + Features.IA + Features.RA),
	AUFDTNIRA (Features.QU + Features.AX + Features.UF + Features.DT + Features.NA + Features.IA + Features.RA),
	AUFFPDTLIRA (Features.QU + Features.AX + Features.UF + Features.FP + Features.DT + Features.LA + Features.IA + Features.RA),
	AUFFPDTNIRA (Features.QU + Features.AX + Features.UF + Features.FP + Features.DT + Features.NA + Features.IA + Features.RA),
	AUFLIA    (Features.QU + Features.AX + Features.UF + Features.LA + Features.IA),
	AUFLIRA   (Features.QU + Features.AX + Features.UF + Features.LA + Features.IA + Features.RA),
	AUFNIA    (Features.QU + Features.AX + Features.UF + Features.NA + Features.IA),
	AUFNIRA   (Features.QU + Features.AX + Features.UF + Features.NA + Features.IA + Features.RA),
	BV        (Features.QU + Features.BV),
	BVFP      (Features.QU + Features.BV + Features.FP),
	BVFPLRA   (Features.QU + Features.BV + Features.FP + Features.LA + Features.RA),
	FP        (Features.QU + Features.FP),
	FPLRA     (Features.QU + Features.FP + Features.LA + Features.RA),
	LIA       (Features.QU + Features.LA + Features.IA),
	LRA       (Features.QU + Features.LA + Features.RA),
	NIA       (Features.QU + Features.NA + Features.IA),
	NRA       (Features.QU + Features.NA + Features.RA),
	UF        (Features.QU + Features.UF),
	UFBV      (Features.QU + Features.UF + Features.BV),
	UFBVDT    (Features.QU + Features.UF + Features.BV + Features.DT),
	UFBVFP    (Features.QU + Features.UF + Features.BV + Features.FP),
	UFBVLIA   (Features.QU + Features.UF + Features.BV + Features.LA + Features.IA),
	UFDT      (Features.QU + Features.UF + Features.DT),
	UFDTLIA   (Features.QU + Features.DT + Features.UF + Features.LA + Features.IA),
	UFDTLIRA  (Features.QU + Features.DT + Features.UF + Features.LA + Features.IA + Features.RA),
	UFDTNIA   (Features.QU + Features.DT + Features.UF + Features.NA + Features.IA),
	UFDTNIRA  (Features.QU + Features.DT + Features.UF + Features.NA + Features.IA + Features.RA),
	UFFPDTLIRA (Features.QU + Features.FP + Features.DT + Features.UF + Features.LA + Features.IA + Features.RA),
	UFFPDTNIRA (Features.QU + Features.FP + Features.DT + Features.UF + Features.NA + Features.IA + Features.RA),
	UFIDL     (Features.QU + Features.UF + Features.DL + Features.IA),
	UFLIA     (Features.QU + Features.UF + Features.LA + Features.IA),
	UFLRA     (Features.QU + Features.UF + Features.LA + Features.RA),
	UFNIA     (Features.QU + Features.UF + Features.NA + Features.IA),
	UFNIRA    (Features.QU + Features.UF + Features.NA + Features.IA + Features.RA),
	UFNRA     (Features.QU + Features.UF + Features.NA + Features.RA),

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
		/** flag for datatypes. */
		static final int DT = (1 << 10);
		/** flag for string theory. */
		static final int S = (1 << 11);
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
