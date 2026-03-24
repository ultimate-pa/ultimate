package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ArithmeticRules;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofRules;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

public class ProofUtils {

	ProofRules mProofRules;

	public ProofUtils(ProofRules rules) {
		mProofRules = rules;
	}

	/**
	 * Resolution rule which handles null proofs (for not resolving).
	 *
	 * @param pivot    The pivot literal.
	 * @param proofPos The proof proving `+ pivot`.
	 * @param proofNeg The proof proving `- pivot`.
	 * @return the combined proof.
	 */
	public Term res(final Term pivot, final Term proofPos, final Term proofNeg) {
		return proofPos == null ? proofNeg
				: proofNeg == null ? proofPos : mProofRules.resolutionRule(pivot, proofPos, proofNeg);
	}

	/**
	 * Checks if a term is an application of an internal function symbol.
	 *
	 * @param funcSym the expected function symbol.
	 * @param term    the term to check.
	 * @return true if term is an application of funcSym.
	 */
	public boolean isApplication(final String funcSym, final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol func = appTerm.getFunction();
			if (func.isIntern() && func.getName().equals(funcSym)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Prove that {@code (= constantTerm canonicalTerm)} where canonicalTerm is a
	 * rational constant, and constantTerm a constant rational term, e.g. a decimal
	 * or a numeral that is not in canonical form.
	 *
	 * @param constantTerm  the constant term
	 * @param canonicalTerm the rational term in canonical form.
	 * @return the proof for the equality.
	 */
	public Term proveConstEquality(final Term constantTerm, final Term canonicalTerm) {
		return proveTrivialEquality(constantTerm, canonicalTerm);
	}

	/**
	 * Prove that {@code (= (- term) canonicalTerm)} where canonicalTerm is a term
	 * in canonical form. On the left hand side, {@code term} should also be in
	 * canonical form .
	 *
	 * @param minusTerm     the unary minus term
	 * @param canonicalTerm the resulting term in canonical form.
	 * @return the proof for the equality.
	 */
	public Term proveUMinusEquality(final Term minusTerm, final Term canonicalTerm) {
		final ApplicationTerm app = (ApplicationTerm) minusTerm;
		assert app.getParameters().length == 1;
		final Term minusToPlus = ArithmeticRules.expandMinus(app.getFunction(), app.getParameters());
		return proveTransitivity(minusTerm, minusToPlus, canonicalTerm, mProofRules.expand(minusTerm),
				mProofRules.polyMul(minusToPlus, canonicalTerm));
	}

	/**
	 * Prove that {@code (= (- term term ...) canonicalTerm)} where canonicalTerm is
	 * a term in canonical form. On the left hand side, {@code term} should also be
	 * in canonical form .
	 *
	 * @param minusTerm     the non-unary minus term
	 * @param canonicalTerm the resulting term in canonical form.
	 * @return the proof for the equality.
	 */
	public Term proveMinusEquality(final Term minusTerm, final Term canonicalTerm) {
		final ApplicationTerm app = (ApplicationTerm) minusTerm;
		final Term[] minusArgs = app.getParameters();
		assert minusArgs.length == 2;
		final Term minusToPlus = ArithmeticRules.expandMinus(app.getFunction(), minusArgs);
		final Theory theory = minusTerm.getTheory();
		final Term[] expectedArgs = new Term[minusArgs.length];
		expectedArgs[0] = minusArgs[0];
		for (int i = 1; i < minusArgs.length; i++) {
			final Polynomial affineTerm = new Polynomial(minusArgs[i]);
			affineTerm.mul(Rational.MONE);
			expectedArgs[i] = affineTerm.toTerm(minusArgs[i].getSort());
		}
		final Term expectedPlus = theory.term(SMTLIBConstants.PLUS, expectedArgs);
		Term proof = mProofRules.expand(minusTerm);
		if (minusToPlus != expectedPlus) {
			proof = proveTransitivity(minusTerm, minusToPlus, expectedPlus, proof,
					mProofRules.cong(minusToPlus, expectedPlus));
			final HashSet<Term> seenEqs = new HashSet<>();
			final Term[] minusToPlusArgs = ((ApplicationTerm) minusToPlus).getParameters();
			for (int i = 0; i < minusToPlusArgs.length; i++) {
				final Term eq = theory.term(SMTLIBConstants.EQUALS, minusToPlusArgs[i], expectedArgs[i]);
				if (seenEqs.add(eq)) {
					final Term proofEq = minusToPlusArgs[i] == expectedArgs[i] ? mProofRules.refl(minusToPlusArgs[i])
							: mProofRules.polyMul(minusToPlusArgs[i], expectedArgs[i]);
					proof = res(eq, proofEq, proof);
				}
			}
		}
		if (expectedPlus != canonicalTerm) {
			proof = proveTransitivity(minusTerm, expectedPlus, canonicalTerm, proof,
					mProofRules.polyAdd(expectedPlus, canonicalTerm));
		}
		return proof;
	}

	/**
	 * Prove that `(= (abs rat) |rat|)` where rat is a rational constant, |rat| is
	 * the rational for the absolute value of rat, and `(abs rat)` is the SMTLIB
	 * function abs applied to rat.
	 *
	 * @param rat  the rational constant
	 * @param sort the sort of the constant.
	 * @return the proof for the equality.
	 */
	public Term proveAbsConstant(final Rational rat, final Sort sort) {
		final Theory theory = sort.getTheory();
		final Term x = rat.toTerm(sort);
		final Term absX = rat.abs().toTerm(sort);
		final Term zero = Rational.ZERO.toTerm(sort);
		final Term ltXZero = theory.term("<", x, zero);
		Term proof = proveAbsEquality(x, absX);
		if (x == absX) {
			proof = res(ltXZero, proof,
					mProofRules.farkas(BigInteger.ONE, ltXZero));
		} else {
			proof = res(ltXZero, mProofRules.total(zero, x), proof);
			final Term leqZeroX = theory.term(SMTLIBConstants.LEQ, zero, x);
			proof = res(leqZeroX, proof,
					mProofRules.farkas(BigInteger.ONE, leqZeroX));
		}
		return proof;
	}

	/**
	 * Prove {@code -(< t 0), +(= (abs t) (- t))} or
	 * {@code +(< t 0), +(= (abs t) t)}.
	 *
	 * @param t    The term whose abs is taken.
	 * @param absT The absolute term t, must be equal to t or (- t).
	 * @return the proof.
	 */
	public Term proveAbsEquality(final Term t, final Term absT) {
		final Theory theory = t.getTheory();
		final Term litAbsT = theory.term(SMTLIBConstants.ABS, t);
		final Term zero = Rational.ZERO.toTerm(t.getSort());
		final Term ltXZero = theory.term("<", t, zero);
		final Term absxDef = theory.term("ite", ltXZero, theory.term("-", t), t);
		Term proof;
		if (t == absT) {
			proof = mProofRules.ite2(absxDef);
		} else {
			proof = mProofRules.ite1(absxDef);
			final Term minusT = theory.term("-", t);
			if (minusT != absT) {
				proof = proveTransitivity(absxDef, minusT, absT, proof, proveUMinusEquality(minusT, absT));
			}
		}
		return proveTransitivity(litAbsT, absxDef, absT, mProofRules.expand(litAbsT), proof);
	}

	/**
	 * Prove that integer terms lhs and rhs are equal, from a proof that not lhs -
	 * rhs >= 1 and not lhs - rhs <= -1.
	 *
	 * @param lhs     an integer term.
	 * @param rhs     an integer term.
	 * @param diff    the term lhs - rhs.
	 * @param proofLt the proof of ~(diff >= 1).
	 * @param proofGt the proof of ~(diff <= -1).
	 * @return the proof of lhs == rhs.
	 */
	private Term proveIntEqualityWithLowHigh(final Term lhs, final Term rhs, final Term diff, final Term proofGt,
			final Term proofLt) {
		final Theory theory = lhs.getTheory();
		final Sort sort = lhs.getSort();
		final Term zero = Rational.ZERO.toTerm(lhs.getSort());
		final Term lhsLtRhs = theory.term(SMTLIBConstants.LT, lhs, rhs);
		final Term lhsGtRhs = theory.term(SMTLIBConstants.LT, rhs, lhs);
		final Term leqZero = theory.term(SMTLIBConstants.LEQ, diff, zero);
		final Term geqZero = theory.term(SMTLIBConstants.LEQ, zero, diff);
		final Term leqMone = theory.term(SMTLIBConstants.LEQ, diff, Rational.MONE.toTerm(sort));
		final Term geqOne = theory.term(SMTLIBConstants.LEQ, Rational.ONE.toTerm(sort), diff);
		return res(lhsLtRhs, res(lhsGtRhs,
				mProofRules.trichotomy(lhs, rhs),
				res(leqZero,
						res(geqOne, mProofRules.totalInt(diff, Rational.ZERO), proofLt),
						mProofRules.farkas(BigInteger.ONE, lhsGtRhs, BigInteger.ONE, leqZero))),
				res(geqZero,
						res(leqMone, mProofRules.totalInt(diff, Rational.ONE.negate()), proofGt),
						mProofRules.farkas(BigInteger.ONE, lhsLtRhs, BigInteger.ONE, geqZero)));
	}

	private Term proveDivEqualityHelper(final Term divTerm, final Term divResult) {
		final Theory theory = divTerm.getTheory();
		final Sort sort = divTerm.getSort();

		assert isApplication("div", divTerm);
		final Term[] divArgs = ((ApplicationTerm) divTerm).getParameters();
		assert divArgs.length == 2;
		final Rational divisor = Polynomial.parseConstant(divArgs[1]);
		assert divisor != null && divisor.isIntegral();

		// check that divResult is really syntactically the result of the division.
		// For (div x c) we compute (1/c * x - divResult), check that it is a constant
		// whose absolute value is less than one and that has the same sign as c.
		final Polynomial poly = new Polynomial();
		poly.add(Rational.MONE, divResult);
		poly.add(divisor.inverse(), divArgs[0]);
		assert poly.isConstant();
		final Rational remainder = poly.getConstant();
		assert remainder.abs().compareTo(Rational.ONE) < 0;
		assert remainder.signum() * divisor.signum() != -1;

		final Term zero = Rational.ZERO.toTerm(sort);
		final Term absDivArg = theory.term(SMTLIBConstants.ABS, divArgs[1]);
		final Term absDivisor = divisor.abs().toTerm(sort);
		final Term origDivLow = theory.term(SMTLIBConstants.LEQ, theory.term(SMTLIBConstants.MUL, divArgs[1], divTerm),
				divArgs[0]);
		final Term origDivHigh = theory.term(SMTLIBConstants.LT, divArgs[0],
				theory.term(SMTLIBConstants.PLUS, theory.term(SMTLIBConstants.MUL, divArgs[1], divTerm), absDivArg));
		final Polynomial diffAffine = new Polynomial(divTerm);
		diffAffine.add(Rational.MONE, divResult);
		final Term diffLhsRhs = diffAffine.toTerm(sort);
		Term proof = mProofRules.trichotomy(divTerm, divResult);
		Term ltLhsRhs = theory.term(SMTLIBConstants.LT, divTerm, divResult);
		Term gtLhsRhs = theory.term(SMTLIBConstants.LT, divResult, divTerm);
		if (divisor.signum() < 0 || remainder.signum() != 0) {
			// we need total-int in the proof
			final Term leqLhsRhs = theory.term(SMTLIBConstants.LEQ, diffLhsRhs, zero);
			final Term geqLhsRhsOne = theory.term(SMTLIBConstants.LEQ, Rational.ONE.toTerm(sort), diffLhsRhs);
			proof = res(gtLhsRhs, proof, mProofRules.farkas(BigInteger.ONE, gtLhsRhs, BigInteger.ONE, leqLhsRhs));
			proof = res(leqLhsRhs, mProofRules.totalInt(diffLhsRhs, Rational.ZERO), proof);
			gtLhsRhs = geqLhsRhsOne;
		}
		if (divisor.signum() > 0 || remainder.signum() != 0) {
			// we need total-int in the proof
			final Term geqLhsRhs = theory.term(SMTLIBConstants.LEQ, zero, diffLhsRhs);
			final Term leqLhsRhsOne = theory.term(SMTLIBConstants.LEQ, diffLhsRhs, Rational.MONE.toTerm(sort));
			proof = res(ltLhsRhs, proof, mProofRules.farkas(BigInteger.ONE, ltLhsRhs, BigInteger.ONE, geqLhsRhs));
			proof = res(geqLhsRhs, mProofRules.totalInt(diffLhsRhs, Rational.ONE.negate()), proof);
			ltLhsRhs = leqLhsRhsOne;
		}
		final Term lhsRhsLow = divisor.signum() > 0 ? gtLhsRhs : ltLhsRhs;
		final Term lhsRhsHigh = divisor.signum() > 0 ? ltLhsRhs : gtLhsRhs;
		final Term eqAbs = theory.term(SMTLIBConstants.EQUALS, absDivArg, absDivisor);
		proof = res(lhsRhsLow, proof,
				mProofRules.farkas(BigInteger.ONE, origDivLow, divisor.abs().numerator(), lhsRhsLow));
		proof = res(lhsRhsHigh, proof, mProofRules.farkas(BigInteger.ONE, origDivHigh, divisor.abs().numerator(),
				lhsRhsHigh, BigInteger.ONE, eqAbs));
		proof = res(eqAbs, proveAbsConstant(divisor, sort), proof);
		proof = res(origDivHigh, mProofRules.divHigh(divArgs[0], divArgs[1]), proof);
		proof = res(origDivLow, mProofRules.divLow(divArgs[0], divArgs[1]), proof);
		return proof;
	}

	/**
	 * Prove that divTerm equals divResult. This works for `div` terms on constants
	 * as well as div on +/- 1 and some special div terms like `(div (+ (* 2 x) 1)
	 * 2)`.
	 *
	 * The condition is that `divTerm` is a term `(div x c)` with non-zero constant
	 * divisor and `(- (* (/ 1 c) x) divResult)` must be a rational constant between
	 * 0 (inclusive) and 1 (exclusive).
	 *
	 * @param divTerm   The div term.
	 * @param divResult The simplified result.
	 * @return the proof for `(= divTerm divResult)`.
	 */
	public Term proveDivEquality(final Term divTerm, final Term divResult) {
		final Theory theory = divTerm.getTheory();
		final Term[] divArgs = ((ApplicationTerm) divTerm).getParameters();
		final Term divEqProof = proveDivEqualityHelper(divTerm, divResult);
		final Term zero = Rational.ZERO.toTerm(divArgs[1].getSort());
		final Term divisorNotZero = proveTrivialDisequality(divArgs[1], zero);
		return res(theory.term(SMTLIBConstants.EQUALS, divArgs[1], zero), divEqProof, divisorNotZero);
	}

	/**
	 * Prove that (div (div a b) c) equals (div a (b*c)), where b,c are non-zero
	 * constants and a an arbitrary term.
	 *
	 * @param divTerm   The (div (div a b) c) term.
	 * @param divResult The simplified result.
	 * @return the proof for `(= divTerm divResult)`.
	 */
	public Term proveDivDiv(final Term divTerm, final Term divResult) {
		final Theory theory = divTerm.getTheory();
		final Sort intSort = divTerm.getSort();
		// prove (div arg0 divisor) - (div arg1 divisor) - poly == 0
		// where poly = 1/d * (arg0 - arg1), provided that poly is an integer term.
		assert isApplication(SMTLIBConstants.DIV, divTerm);
		final Term[] div1Args = ((ApplicationTerm) divTerm).getParameters();
		assert isApplication(SMTLIBConstants.DIV, div1Args[0]);
		final Term div2Term = div1Args[0];
		final Term[] div2Args = ((ApplicationTerm) div2Term).getParameters();
		assert isApplication(SMTLIBConstants.DIV, divResult);
		final Term[] div3Args = ((ApplicationTerm) divResult).getParameters();
		assert div2Args[0] == div3Args[0];
		final Term arg = div2Args[0];

		final Rational divisor1 = Polynomial.parseConstant(div1Args[1]);
		final Rational divisor2 = Polynomial.parseConstant(div2Args[1]);
		final Rational divisor3 = Polynomial.parseConstant(div3Args[1]);
		assert divisor1.isIntegral();
		assert divisor2.isIntegral();
		assert divisor2.signum() > 0;
		assert divisor1.signum() != 0;
		assert divisor1.mul(divisor2).equals(divisor3);

		final Polynomial poly = new Polynomial(divTerm);
		poly.add(Rational.MONE, divResult);
		final Term diff = poly.toTerm(intSort);
		final Term zero = Rational.ZERO.toTerm(intSort);

		final Term absDiv1 = theory.term(SMTLIBConstants.ABS, div1Args[1]);
		final Term absDiv2 = theory.term(SMTLIBConstants.ABS, div2Args[1]);
		final Term absDiv3 = theory.term(SMTLIBConstants.ABS, div3Args[1]);
		final Term absDiv1Eq = theory.term(SMTLIBConstants.EQUALS, absDiv1, divisor1.abs().toTerm(intSort));
		final Term absDiv2Eq = theory.term(SMTLIBConstants.EQUALS, absDiv2, div2Args[1]);
		final Term absDiv3Eq = theory.term(SMTLIBConstants.EQUALS, absDiv3, divisor3.abs().toTerm(intSort));
		final Term mulDiv1 = theory.term(SMTLIBConstants.MUL, div1Args[1], divTerm);
		final Term mulDiv2 = theory.term(SMTLIBConstants.MUL, div2Args[1], div2Term);
		final Term mulDiv3 = theory.term(SMTLIBConstants.MUL, div3Args[1], divResult);
		final Term div1Low = theory.term(SMTLIBConstants.LEQ, mulDiv1, div2Term);
		final Term div2Low = theory.term(SMTLIBConstants.LEQ, mulDiv2, arg);
		final Term div3Low = theory.term(SMTLIBConstants.LEQ, mulDiv3, arg);
		final Term div1High = theory.term(SMTLIBConstants.LT, div2Term,
				theory.term(SMTLIBConstants.PLUS, mulDiv1, absDiv1));
		final Term div2High = theory.term(SMTLIBConstants.LT, arg,
				theory.term(SMTLIBConstants.PLUS, mulDiv2, absDiv2));
		final Term div3High = theory.term(SMTLIBConstants.LT, arg,
				theory.term(SMTLIBConstants.PLUS, mulDiv3, absDiv3));
		final Polynomial div1HighPoly = new Polynomial(div2Term);
		div1HighPoly.add(divisor1.negate(), divTerm);
		div1HighPoly.add(divisor1.abs().sub(Rational.ONE).negate());
		final Term div1HighDiff = div1HighPoly.toTerm(intSort);
		final Term div1HighStrong = theory.term(SMTLIBConstants.LEQ, div1HighDiff, zero);

		final Term leqm1 = theory.term(SMTLIBConstants.LEQ, diff, Rational.MONE.toTerm(intSort));
		final Term geq1 = theory.term(SMTLIBConstants.LEQ, Rational.ONE.toTerm(intSort), diff);

		Term proofGt, proofLt;
		proofGt = res(absDiv3Eq, proveAbsConstant(divisor3, intSort),
				res(div1Low, mProofRules.divLow(div2Term, div1Args[1]),
				res(div2Low, mProofRules.divLow(arg, div2Args[1]),
						res(div3High, mProofRules.divHigh(arg, div3Args[1]), mProofRules.farkas(
										divisor2.numerator(), div1Low, BigInteger.ONE, div2Low,
												BigInteger.ONE, div3High, BigInteger.ONE, absDiv3Eq,
										divisor3.abs().numerator(), divisor3.signum() > 0 ? geq1 : leqm1)))));
		final Term div1HighGeq = theory.term(SMTLIBConstants.LEQ, Rational.ONE.toTerm(intSort), div1HighDiff);
		final Term div1HighStrongProof =
				res(absDiv1Eq, proveAbsConstant(divisor1, intSort),
				res(div1High, mProofRules.divHigh(div2Term, div1Args[1]),
								res(div1HighGeq, mProofRules.totalInt(div1HighDiff, Rational.ZERO),
										mProofRules.farkas(BigInteger.ONE, div1HighGeq, BigInteger.ONE, div1High,
												BigInteger.ONE, absDiv1Eq))));
		proofLt = res(absDiv2Eq, proveAbsConstant(divisor2, intSort),
					res(div1HighStrong, div1HighStrongProof,
					res(div2High, mProofRules.divHigh(arg, div2Args[1]),
								res(div3Low, mProofRules.divLow(arg, div3Args[1]),
										mProofRules.farkas(divisor2.numerator(), div1HighStrong, BigInteger.ONE,
												div2High, BigInteger.ONE, div3Low, BigInteger.ONE, absDiv2Eq,
												divisor3.abs().numerator(), divisor3.signum() > 0 ? leqm1 : geq1)))));

		Term proof = proveIntEqualityWithLowHigh(divTerm, divResult, diff,
				divisor3.signum() > 0 ? proofLt : proofGt,
				divisor3.signum() > 0 ? proofGt : proofLt);
		proof = res(theory.term(SMTLIBConstants.EQUALS, div1Args[1], zero), proof,
				proveTrivialDisequality(div1Args[1], zero));
		if (div1Args[1] != div2Args[1]) {
			proof = res(theory.term(SMTLIBConstants.EQUALS, div2Args[1], zero), proof,
					proveTrivialDisequality(div2Args[1], zero));
		}
		proof = res(theory.term(SMTLIBConstants.EQUALS, div3Args[1], zero), proof,
				proveTrivialDisequality(div3Args[1], zero));
		return proof;
	}

	/**
	 * Prove that modTerm equals modResult. This works for `mod` terms on constants
	 * as well as div on +/- 1 and some special mod terms like `(mod (+ (* 2 x) 1)
	 * 2)`.
	 *
	 * The condition is that `modTerm` is a term `(mod x c)` with non-zero constant
	 * divisor, `modResult` is an integer constant between 0 and |c|, and `(* (/ 1
	 * c) (- x modResult))` must have only integer coefficients.
	 *
	 * @param modTerm   The mod term.
	 * @param modResult The simplified result.
	 * @return the proof for `(= modTerm modResult)`.
	 */
	public Term proveModConstant(final Term modTerm, final Term modResult) {
		final Theory theory = modTerm.getTheory();
		final Sort sort = modTerm.getSort();

		assert isApplication("mod", modTerm);
		final Term[] divArgs = ((ApplicationTerm) modTerm).getParameters();
		assert divArgs.length == 2;
		final Rational divisor = Polynomial.parseConstant(divArgs[1]);
		assert divisor != null && divisor.isIntegral();

		final Polynomial poly = new Polynomial();
		poly.add(divisor.inverse(), divArgs[0]);
		final Rational modulo = Polynomial.parseConstant(modResult);
		assert modulo.signum() >= 0;
		assert modulo.compareTo(divisor.abs()) < 0;
		poly.add(modulo.div(divisor).negate());

		assert poly.getGcd().isIntegral();
		final Term divResult = poly.toTerm(sort);
		final Term divTerm = theory.term(SMTLIBConstants.DIV, divArgs);

		final Term divEqProof = proveDivEqualityHelper(divTerm, divResult);
		final Term divModEqProof = mProofRules.modDef(divArgs[0], divArgs[1]);
		final Term divEq = theory.term(SMTLIBConstants.EQUALS, divTerm, divResult);
		final Term divModEq = theory.term(SMTLIBConstants.EQUALS,
				theory.term(SMTLIBConstants.PLUS,
						theory.term(SMTLIBConstants.MUL, divArgs[1], divTerm), modTerm),
				divArgs[0]);
		final Term modEq = theory.term(SMTLIBConstants.EQUALS, modTerm, modResult);

		final Term zero = Rational.ZERO.toTerm(divArgs[1].getSort());
		final Term divisorNotZero = proveTrivialDisequality(divArgs[1], zero);
		return res(theory.term(SMTLIBConstants.EQUALS, divArgs[1], zero), res(divEq, divEqProof,
				res(divModEq, divModEqProof, proveEqualityFromEqualities(new Term[] { modEq, divEq, divModEq },
						new BigInteger[] { BigInteger.ONE, divisor.numerator(), BigInteger.ONE.negate() }))),
				divisorNotZero);
	}

	public Term proveDivModHelper(Term arg0, Term arg1, Term divisorTerm) {
		final Theory theory = arg0.getTheory();
		final Sort intSort = arg0.getSort();
		// prove (div arg0 divisor) - (div arg1 divisor) - poly == 0
		// where poly = 1/d * (arg0 - arg1), provided that poly is an integer term.
		final Rational divisor = Polynomial.parseConstant(divisorTerm);
		final Polynomial poly = new Polynomial(arg0);
		poly.add(Rational.MONE, arg1);
		poly.mul(divisor.inverse());
		assert divisor.isIntegral();
		assert poly.isAllIntSummands();
		assert poly.getGcd().isIntegral();

		final Term div0 = theory.term(SMTLIBConstants.DIV, arg0, divisorTerm);
		final Term div1 = theory.term(SMTLIBConstants.DIV, arg1, divisorTerm);
		final Polynomial divDiffMinusPoly = new Polynomial(div0);
		divDiffMinusPoly.add(Rational.MONE, div1);
		divDiffMinusPoly.add(Rational.MONE, poly);
		final Term lhs = divDiffMinusPoly.toTerm(intSort);
		final Term zero = Rational.ZERO.toTerm(intSort);


		final Term absDiv = theory.term(SMTLIBConstants.ABS, divisorTerm);
		final Term absDivEq = theory.term(SMTLIBConstants.EQUALS, absDiv, divisor.abs().toTerm(intSort));
		final Term mulDiv0 = theory.term(SMTLIBConstants.MUL, divisorTerm, div0);
		final Term mulDiv1 = theory.term(SMTLIBConstants.MUL, divisorTerm, div1);
		final Term div0Low = theory.term(SMTLIBConstants.LEQ, mulDiv0, arg0);
		final Term div0High = theory.term(SMTLIBConstants.LT, arg0, theory.term(SMTLIBConstants.PLUS, mulDiv0, absDiv));
		final Term div1Low = theory.term(SMTLIBConstants.LEQ, mulDiv1, arg1);
		final Term div1High = theory.term(SMTLIBConstants.LT, arg1, theory.term(SMTLIBConstants.PLUS, mulDiv1, absDiv));

		final Term leqm1 = theory.term(SMTLIBConstants.LEQ, lhs, Rational.MONE.toTerm(intSort));
		final Term geq1 = theory.term(SMTLIBConstants.LEQ, Rational.ONE.toTerm(intSort), lhs);

		Term proofGt, proofLt;
		proofGt = res(div0Low, mProofRules.divLow(arg0, divisorTerm),
				res(div1High, mProofRules.divHigh(arg1, divisorTerm), mProofRules.farkas(
						BigInteger.ONE, div0Low, BigInteger.ONE, div1High, BigInteger.ONE, absDivEq,
						divisor.numerator(), divisor.signum() > 0 ? geq1 : leqm1)));
		proofLt = res(div1Low, mProofRules.divLow(arg1, divisorTerm),
				res(div0High, mProofRules.divHigh(arg0, divisorTerm), mProofRules.farkas(
						BigInteger.ONE, div0High, BigInteger.ONE, div1Low, BigInteger.ONE, absDivEq,
						divisor.numerator(), divisor.signum() > 0 ? leqm1 : geq1)));
		return res(absDivEq, proveAbsConstant(divisor, intSort),
				proveIntEqualityWithLowHigh(lhs, zero, lhs, divisor.signum() > 0 ? proofLt : proofGt,
						divisor.signum() > 0 ? proofGt : proofLt));
	}

	public Term proveModToDiv(Term modTerm, Term rhs) {
		// modulo: (mod x c) -> (- x' (* c (div x' c)))
		// where x'-x is divisible by c.
		assert isApplication("mod", modTerm);
		final Theory theory = modTerm.getTheory();
		final Term[] modArgs = ((ApplicationTerm) modTerm).getParameters();
		assert modArgs.length == 2;
		assert modArgs[1] instanceof ConstantTerm;
		final Rational modulus = (Rational) ((ConstantTerm) modArgs[1]).getValue();

		final Polynomial rhsPoly = new Polynomial(rhs);
		// find div term;
		final Term div0Term = theory.term(SMTLIBConstants.DIV, modArgs);
		Term arg1 = null;
		ApplicationTerm div1Term = null;
		for (final Map.Entry<Map<Term, Integer>, Rational> summand : rhsPoly.getSummands().entrySet()) {
			if (summand.getValue().negate().equals(modulus) && summand.getKey().size() == 1) {
				final Map.Entry<Term, Integer> monoid = summand.getKey().entrySet().iterator().next();
				if (monoid.getValue() == 1 && isApplication(SMTLIBConstants.DIV, monoid.getKey())) {
					final ApplicationTerm appTerm = (ApplicationTerm) monoid.getKey();
					if (appTerm.getParameters()[1] == modArgs[1]) {
						arg1 = appTerm.getParameters()[0];
						final Polynomial test = new Polynomial(arg1);
						test.add(modulus.negate(), appTerm);
						if (test.equals(rhsPoly)) {
							div1Term = appTerm;
							break;
						}
					}
				}
			}
		}
		assert div1Term != null;

		final Sort intSort = modTerm.getSort();
		final Term zero = Rational.ZERO.toTerm(intSort);
		final Term divEqZero = theory.term(SMTLIBConstants.EQUALS, modArgs[1], zero);
		final Term divPlusMod0 = theory.term(SMTLIBConstants.PLUS,
				theory.term(SMTLIBConstants.MUL, modArgs[1], div0Term), modTerm);
		final Term divPlusMod0Eq = theory.term(SMTLIBConstants.EQUALS, divPlusMod0, modArgs[0]);

		Term proof;
		if (div0Term == div1Term) {
			proof = proveEqualityFromEqualities(
					new Term[] { theory.term(SMTLIBConstants.EQUALS, modTerm, rhs), divPlusMod0Eq },
					new BigInteger[] { BigInteger.ONE, BigInteger.ONE.negate() });
		} else {
			final Rational divisor = Polynomial.parseConstant(modArgs[1]);
			final Polynomial poly = new Polynomial(div0Term);
			poly.add(Rational.MONE, div1Term);
			poly.add(divisor.inverse().negate(), modArgs[0]);
			poly.add(divisor.inverse(), arg1);

			final Term divDiffMinusPoly = poly.toTerm(intSort);
			final Term divDiffMinusPolyEq = theory.term(SMTLIBConstants.EQUALS, divDiffMinusPoly, zero);
			proof = proveEqualityFromEqualities(
					new Term[] { theory.term(SMTLIBConstants.EQUALS, modTerm, rhs), divDiffMinusPolyEq, divPlusMod0Eq },
					new BigInteger[] { BigInteger.ONE, divisor.numerator(), BigInteger.ONE.negate(), });
			proof = res(divDiffMinusPolyEq, proveDivModHelper(modArgs[0], arg1, modArgs[1]), proof);
		}
		return res(divEqZero,
				res(divPlusMod0Eq, mProofRules.modDef(modArgs[0], modArgs[1]), proof),
				proveTrivialDisequality(modArgs[1], zero));
	}

	public Term proveModNormalize(Term lhs, Term rhs) {
		if (rhs instanceof ConstantTerm) {
			return proveModConstant(lhs, rhs);
		} else {
			return proveModToDiv(lhs, rhs);
		}
	}

	public Term proveToIntConstant(Term funcTerm, Term result) {
		final Theory theory = funcTerm.getTheory();

		assert isApplication("to_int", funcTerm);
		final Term arg = ((ApplicationTerm) funcTerm).getParameters()[0];
		final Rational argRational = Polynomial.parseConstant(arg);
		final Rational argFloor = argRational.floor();

		final Term toReal = theory.term(SMTLIBConstants.TO_REAL, funcTerm);
		final Term oneReal = Rational.ONE.toTerm(toReal.getSort());
		final Term toRealPlus1 = theory.term(SMTLIBConstants.PLUS, toReal, oneReal);
		final Term resultPlus1 = argRational.floor().add(Rational.ONE).toTerm(result.getSort());
		final Term resultMinus1 = argRational.floor().sub(Rational.ONE).toTerm(result.getSort());

		final Term argLtToIntPlus1 = theory.term(SMTLIBConstants.LT, arg, toRealPlus1);
		final Term toIntLeqResultMinus1 = theory.term(SMTLIBConstants.LEQ, funcTerm, resultMinus1);
		final Term resultLeqToInt = theory.term(SMTLIBConstants.LEQ, result, funcTerm);
		final Term toIntLtResult = theory.term(SMTLIBConstants.LT, funcTerm, result);


		final Term proof1 = res(resultLeqToInt,
				res(toIntLeqResultMinus1, mProofRules.totalInt(funcTerm, argFloor.sub(Rational.ONE)),
				res(argLtToIntPlus1, mProofRules.toIntHigh(arg),
								mProofRules.farkas(BigInteger.ONE, toIntLeqResultMinus1, BigInteger.ONE,
										argLtToIntPlus1))),
				mProofRules.farkas(BigInteger.ONE, toIntLtResult, BigInteger.ONE, resultLeqToInt));

		final Term toIntLeqArg = theory.term(SMTLIBConstants.LEQ, toReal, arg);
		final Term resultPlus1LeqToInt = theory.term(SMTLIBConstants.LEQ, resultPlus1, funcTerm);
		final Term toIntLeqResult = theory.term(SMTLIBConstants.LEQ, funcTerm, result);
		final Term resultLtToInt = theory.term(SMTLIBConstants.LT, result, funcTerm);

		final Term proof2 = res(toIntLeqResult,
				res(resultPlus1LeqToInt, mProofRules.totalInt(funcTerm, argFloor),
						res(toIntLeqArg, mProofRules.toIntLow(arg),
								mProofRules.farkas(BigInteger.ONE, resultPlus1LeqToInt, BigInteger.ONE, toIntLeqArg))),
				mProofRules.farkas(BigInteger.ONE, resultLtToInt, BigInteger.ONE, toIntLeqResult));

		return res(resultLtToInt, res(toIntLtResult, mProofRules.trichotomy(funcTerm, result), proof1), proof2);
	}

	/**
	 * Prove that first and second are equal (modulo order of operands for +).
	 *
	 * @param first  the left-hand side of the equality
	 * @param second the right-hand side of the equality
	 * @return the proof for `(= first second)`.
	 */
	public Term proveTrivialEquality(final Term first, final Term second) {
		if (first == second) {
			return mProofRules.refl(first);
		}
		final Theory theory = first.getTheory();
		final Term ltTerm = theory.term(SMTLIBConstants.LT, first, second);
		final Term gtTerm = theory.term(SMTLIBConstants.LT, second, first);
		return res(ltTerm,
				res(gtTerm, mProofRules.trichotomy(first, second), mProofRules.farkas(BigInteger.ONE, gtTerm)),
				mProofRules.farkas(BigInteger.ONE, ltTerm));
	}

	/**
	 * Prove that the disequality between two terms is trivial. There are two cases,
	 * (1) the difference between the terms is constant and nonzero, e.g.
	 * {@code (= x (+ x 1))}, or (2) the difference contains only integer variables
	 * and the constant divided by the gcd of the factors is non-integral, e.g.,
	 * {@code (= (+ x (* 2 y)) (+ x (* 2 z) 1))}.
	 *
	 * @param first  the left-hand side of the equality
	 * @param second the right-hand side of the equality
	 * @return the proof for `~(= first second)` or null if this is not a trivial
	 *         disequality.
	 */
	public Term proveTrivialDisequality(final Term first, final Term second) {
		final Theory theory = first.getTheory();
		final Polynomial diff = new Polynomial(first);
		diff.add(Rational.MONE, second);
		if (diff.isConstant()) {
			if (diff.getConstant().signum() > 0) {
				final Term eqLhs = theory.term(SMTLIBConstants.EQUALS, first, second);
				return mProofRules.farkas(BigInteger.ONE, eqLhs);
			} else {
				assert (diff.getConstant().signum() < 0);
				final Term eqSwapped = theory.term(SMTLIBConstants.EQUALS, second, first);
				return mProofRules.resolutionRule(eqSwapped, mProofRules.symm(second, first),
						mProofRules.farkas(BigInteger.ONE, eqSwapped));
			}
		} else {
			final Rational gcd = diff.getGcd();
			diff.mul(gcd.inverse());
			final Rational bound = diff.getConstant().negate();
			if (!diff.isAllIntSummands() || bound.isIntegral()) {
				return null;
			}
			final Sort intSort = theory.getSort(SMTLIBConstants.INT);
			diff.add(bound);
			final Term intVar = diff.toTerm(intSort);
			final Term floorBound = bound.floor().toTerm(intSort);
			final Term ceilBound = bound.ceil().toTerm(intSort);
			assert ceilBound != floorBound;
			// show (ceil(bound) <= intVar) || (intVar <= floor(bound)
			final Term geqCeil = theory.term(SMTLIBConstants.LEQ, ceilBound, intVar);
			final Term leqFloor = theory.term(SMTLIBConstants.LEQ, intVar, floorBound);
			final Term proofIntCase = mProofRules.totalInt(intVar, bound.floor());
			// show inequality in both cases
			final Term eqLhs = theory.term(SMTLIBConstants.EQUALS, first, second);
			final Term eqSwapped = theory.term(SMTLIBConstants.EQUALS, second, first);
			final Term caseCeil = mProofRules.farkas(gcd.denominator(), eqLhs, gcd.numerator(), geqCeil);
			final Term caseFloor = mProofRules.resolutionRule(eqSwapped, mProofRules.symm(second, first),
					mProofRules.farkas(gcd.denominator(), eqSwapped, gcd.numerator(), leqFloor));
			return mProofRules.resolutionRule(leqFloor, mProofRules.resolutionRule(geqCeil, proofIntCase, caseCeil),
					caseFloor);
		}
	}

	/**
	 * Proof a linear equality eqs[0] from other equalities eqs[1],...eq[n].
	 * The coeffs must be chosen such that sum coeffs[i]*eq[i] evaluates to a trivial equality,
	 * with both sides being equal.
	 * @param eqs The equality terms that are combined. eqs[0] is the equality that is proved.
	 * @param coeffs The farkas coefficients; they can be negative.
	 * @return the proof for eqs[0] from eqs[1],...,eqs[n].
	 */
	public Term proveEqualityFromEqualities(final Term[] eqs, final BigInteger[] coeffs) {
		final Theory theory = eqs[0].getTheory();
		assert eqs.length == coeffs.length;
		final Object[] farkas1 = new Object[2 * coeffs.length];
		final Object[] farkas2 = new Object[2 * coeffs.length];
		for (int i = 0; i < coeffs.length; i++) {
			final Term[] eqArgs = ((ApplicationTerm) eqs[i]).getParameters();
			final Term t1 = i == 0 ? theory.term(SMTLIBConstants.LT, eqArgs[0], eqArgs[1]) : eqs[i];
			final Term t2 = theory.term(i == 0 ? SMTLIBConstants.LT : SMTLIBConstants.EQUALS, eqArgs[1], eqArgs[0]);
			farkas1[2 * i] = coeffs[i].abs();
			farkas1[2 * i + 1] = coeffs[i].signum() > 0 ? t1 : t2;
			farkas2[2 * i] = coeffs[i].abs();
			farkas2[2 * i + 1] = coeffs[i].signum() > 0 ? t2 : t1;
		}
		final Term[] eq0Args = ((ApplicationTerm) eqs[0]).getParameters();
		Term proof = res((Term) farkas1[1],
				res((Term) farkas2[1], mProofRules.trichotomy(eq0Args[0], eq0Args[1]), mProofRules.farkas(farkas2)),
				mProofRules.farkas(farkas1));
		for (int i = 1; i < coeffs.length; i++) {
			final Term[] eqArgs = ((ApplicationTerm) eqs[i]).getParameters();
			final Term eqSwapped = theory.term(SMTLIBConstants.EQUALS, eqArgs[1], eqArgs[0]);
			proof = res(eqSwapped, mProofRules.symm(eqArgs[1], eqArgs[0]), proof);
		}
		return proof;
	}

	/**
	 * Proof a linear equality rhs from a linear equality lhs. This proves
	 *
	 * <pre>
	 * (=&gt; (= lhs[0] lhs[1]) (= rhs[0] rhs[1])
	 * </pre>
	 *
	 * where (lhs[0] - lhs[1]) * multiplier == (rhs[0] - rhs[1]).
	 *
	 * @param lhs        the terms that are known to be equal
	 * @param rhs        the terms that should be proved to be equal.
	 * @param multiplier the factor that makes the sides equal.
	 * @return the proof.
	 */
	public Term proveEqWithMultiplier(final Term[] lhs, final Term[] rhs, final Rational multiplier) {
		final Theory theory = lhs[0].getTheory();
		return proveEqualityFromEqualities(
				new Term[] { theory.term(SMTLIBConstants.EQUALS, rhs[0], rhs[1]),
						theory.term(SMTLIBConstants.EQUALS, lhs[0], lhs[1]) },
				new BigInteger[] { multiplier.denominator(), multiplier.numerator().negate() });
	}

	/**
	 * Prove that {@code (= (/ term constant) canonicalTerm)} where canonicalTerm is
	 * a term in canonical form. On the left hand side, {@code term} should also be
	 * in canonical form .
	 *
	 * @param divideTerm    the divide term
	 * @param canonicalTerm the resulting term in canonical form.
	 * @return the proof for the equality.
	 */
	public Term proveDivideEquality(Term divideTerm, Term canonicalTerm) {
		assert isApplication(SMTLIBConstants.DIVIDE, divideTerm);
		final Theory theory = divideTerm.getTheory();
		final Term[] divideArgs = ((ApplicationTerm) divideTerm).getParameters();
		Term proofDivDef = mProofRules.divideDef(divideArgs);
		final Sort sort = divideTerm.getSort();
		final Term zero = Rational.ZERO.toTerm(sort);
		final Term[] mulTermArgs = new Term[divideArgs.length];
		Rational multiplier = Rational.ONE;
		for (int i = 1; i < divideArgs.length; i++) {
			final Term eqZero = theory.term(SMTLIBConstants.EQUALS, divideArgs[i], zero);
			proofDivDef = res(eqZero, proofDivDef, proveTrivialDisequality(divideArgs[i], zero));
			multiplier = multiplier.mul(Polynomial.parseConstant(divideArgs[i]));
			mulTermArgs[i - 1] = divideArgs[i];
		}
		mulTermArgs[mulTermArgs.length - 1] = divideTerm;
		Term mulTerm = theory.term("*", mulTermArgs);
		if (mulTermArgs.length > 2) {
			final Term mulShortTerm = theory.term("*", multiplier.toTerm(sort), divideTerm);
			proofDivDef = proveTransitivity(mulShortTerm, mulTerm, divideArgs[0],
					res(theory.term(SMTLIBConstants.EQUALS, mulTerm, mulShortTerm),
							mProofRules.polyMul(mulTerm, mulShortTerm), mProofRules.symm(mulShortTerm, mulTerm)),
					proofDivDef);
			mulTerm = mulShortTerm;
		}
		// now mulTerm is (* multiplier lhs)
		// and proofDivDef is a proof for (= mulTerm lhsArgs[0])
		return res(theory.term(SMTLIBConstants.EQUALS, mulTerm, divideArgs[0]), proofDivDef, proveEqWithMultiplier(
				new Term[] { mulTerm, divideArgs[0] }, new Term[] { divideTerm, canonicalTerm }, multiplier.inverse()));
	}

	/**
	 * Prove the equality (= ((_ int_to_bv bitLength) nat) (_ bvnat bitLength)).
	 * Here bvnat is the canonic constant bitvector form.
	 *
	 * @param nat       a constant numeric term.
	 * @param bitLength the bit-vector length.
	 * @return the proof of the equality.
	 */
	public Term proveIntToBvConstant(final Term nat, BigInteger bitLength) {
		final Theory theory = nat.getTheory();
		final Sort intSort = theory.getSort(SMTLIBConstants.INT);
		final BigInteger val = Polynomial.parseConstant(nat).numerator();
		final BigInteger pow2 = BigInteger.ONE.shiftLeft(bitLength.intValue());
		final BigInteger modVal = val.mod(pow2);
		final Sort bvSort = theory.getSort(SMTLIBConstants.BITVEC, new String[] { bitLength.toString() });
		final Term bv = theory.constant(modVal, bvSort);
		final Term bvnat = theory.term(SMTLIBConstants.INT_TO_BV, bvSort.getIndices(), null, nat);
		if (modVal == val) {
			return res(theory.term(SMTLIBConstants.EQUALS, bv, bvnat), mProofRules.bvConst(modVal, bitLength),
					mProofRules.symm(bvnat, bv));
		} else {
			final Term intbvnat = theory.term(SMTLIBConstants.UBV_TO_INT, bvnat);
			final Term bvintbvnat = theory.term(SMTLIBConstants.INT_TO_BV, bvSort.getIndices(), null, intbvnat);
			final Term modValTerm = Rational.valueOf(modVal, BigInteger.ONE).toTerm(intSort);
			final Term bvModVal = theory.term(SMTLIBConstants.INT_TO_BV, bvSort.getIndices(), null, modValTerm);

			return res(theory.term(SMTLIBConstants.EQUALS, bvnat, bvintbvnat),
				res(theory.term(SMTLIBConstants.EQUALS, bvintbvnat, bvnat),
							mProofRules.ubv2int2bv(bvnat), mProofRules.symm(bvnat, bvintbvnat)),
				res(theory.term(SMTLIBConstants.EQUALS, bvintbvnat, bvModVal),
							res(theory.term(SMTLIBConstants.EQUALS, intbvnat, modValTerm),
								proveIntToUbvToIntConstant(nat, bitLength),
								mProofRules.cong(bvintbvnat, bvModVal)),
						res(theory.term(SMTLIBConstants.EQUALS, bvModVal, bv),
							res(theory.term(SMTLIBConstants.EQUALS, bv, bvModVal),
									mProofRules.bvConst(modVal, bitLength),
									mProofRules.symm(bvModVal, bv)),
							mProofRules.trans(bvnat, bvintbvnat, bvModVal, bv))));
		}
	}

	/**
	 * Prove the equality (= (ubv_to_int (int_to_bv nat)) natModPow2).
	 *
	 * @param nat       a constant integer term.
	 * @param bitLength the length of the intermediate bit-vector.
	 * @return the proof of the equality.
	 */
	public Term proveIntToUbvToIntConstant(final Term nat, BigInteger bitLength) {
		final Theory theory = nat.getTheory();
		final Sort intSort = nat.getSort();
		assert intSort.getName() == SMTLIBConstants.INT;
		final BigInteger val = Polynomial.parseConstant(nat).numerator();
		final Term bvnat = theory.term(SMTLIBConstants.INT_TO_BV, new String[] { bitLength.toString() }, null, nat);
		final Term intbvnat = theory.term(SMTLIBConstants.UBV_TO_INT, bvnat);
		final BigInteger pow2 = BigInteger.ONE.shiftLeft(bitLength.intValue());
		final Term pow2Term = Rational.valueOf(pow2, BigInteger.ONE).toTerm(intSort);
		final Term modNat = theory.term(SMTLIBConstants.MOD, nat, pow2Term);
		final Term natModPow2 = Rational.valueOf(val.mod(pow2), BigInteger.ONE).toTerm(intSort);
		return proveTransitivity(intbvnat, modNat, natModPow2, mProofRules.int2ubv2int(bitLength, nat),
				proveModConstant(modNat, natModPow2));
	}

	/**
	 * Prove the equality (= (ubv_to_int bv) const).
	 *
	 * @param bv A bitvector constant of the form `(_ bvConst bitLength)`
	 * @return the proof of the equality.
	 */
	public Term proveUbvToIntConstant(final Term bv) {
		final Theory theory = bv.getTheory();
		final Sort intSort = theory.getSort(SMTLIBConstants.INT);
		final BigInteger val = (BigInteger) ((ConstantTerm) bv).getValue();
		final Term nat = Rational.valueOf(val, BigInteger.ONE).toTerm(intSort);
		final Term intbv = theory.term(SMTLIBConstants.UBV_TO_INT, bv);
		final Term bvnat = theory.term(SMTLIBConstants.INT_TO_BV, bv.getSort().getIndices(), null, nat);
		final Term intbvnat = theory.term(SMTLIBConstants.UBV_TO_INT, bvnat);
		final BigInteger bitLength = new BigInteger(bv.getSort().getIndices()[0]);
		final BigInteger pow2 = BigInteger.ONE.shiftLeft(bitLength.intValue());
		final Term pow2Term = Rational.valueOf(pow2, BigInteger.ONE).toTerm(intSort);
		final Term modNat = theory.term(SMTLIBConstants.MOD, nat, pow2Term);
		return res(theory.term(SMTLIBConstants.EQUALS, intbv, intbvnat),
				res(theory.term(SMTLIBConstants.EQUALS, bv, bvnat),
						mProofRules.bvConst(val, bitLength), mProofRules.cong(intbv, intbvnat)),
				res(theory.term(SMTLIBConstants.EQUALS, intbvnat, modNat),
					mProofRules.int2ubv2int(bitLength, nat),
					res(theory.term(SMTLIBConstants.EQUALS, modNat, nat), proveModConstant(modNat, nat),
								mProofRules.trans(intbv, intbvnat, modNat, nat))));
	}

	/**
	 * Prove the equality (= (sbv_to_int bv) const).
	 *
	 * @param bv A bitvector constant of the form `(_ bvConst bitLength)`
	 * @return the proof of the equality.
	 */
	public Term proveSbvToIntConstant(final Term bv) {
		final Theory theory = bv.getTheory();
		final Sort intSort = theory.getSort(SMTLIBConstants.INT);
		final BigInteger val = (BigInteger) ((ConstantTerm) bv).getValue();
		final Rational uvalue = Rational.valueOf(val, BigInteger.ONE);
		final Term nat = uvalue.toTerm(intSort);
		final Term intbv = theory.term(SMTLIBConstants.SBV_TO_INT, bv);
		final Term bvnat = theory.term(SMTLIBConstants.INT_TO_BV, bv.getSort().getIndices(), null, nat);
		final Term intbvnat = theory.term(SMTLIBConstants.SBV_TO_INT, bvnat);
		final int bitLength = Integer.parseInt(bv.getSort().getIndices()[0]);
		final Rational pow2 = Rational.valueOf(BigInteger.ONE.shiftLeft(bitLength), BigInteger.ONE);
		final Rational pow2Half = Rational.valueOf(BigInteger.ONE.shiftLeft(bitLength - 1), BigInteger.ONE);
		final Term pow2Term = pow2.toTerm(intSort);
		final Term added = theory.term(SMTLIBConstants.PLUS, nat, pow2Half.toTerm(intSort));
		final Rational addedValue = uvalue.add(pow2Half);
		final Term addedValueTerm = addedValue.toTerm(intSort);
		final Term modNat = theory.term(SMTLIBConstants.MOD, added, pow2Term);
		final Term mod2Nat = theory.term(SMTLIBConstants.MOD, addedValue.toTerm(intSort), pow2Term);
		final Rational moddedValue = uvalue.compareTo(pow2Half) >= 0 ? addedValue.sub(pow2) : addedValue;
		final Term moddedValueTerm = moddedValue.toTerm(intSort);
		final Term mod1Proof =
				res(theory.term(SMTLIBConstants.EQUALS, pow2Term, pow2Term), mProofRules.refl(pow2Term),
						res(theory.term(SMTLIBConstants.EQUALS, added, addedValueTerm),
								mProofRules.polyAdd(added, addedValueTerm), mProofRules.cong(modNat, mod2Nat)));
		final Term modProof = proveTransitivity(modNat, mod2Nat, moddedValueTerm, mod1Proof,
				proveModConstant(mod2Nat, moddedValueTerm));
		final Term subTerm = theory.term(SMTLIBConstants.PLUS, modNat, pow2Half.negate().toTerm(intSort));
		final Term sub2Term = theory.term(SMTLIBConstants.PLUS, moddedValueTerm, pow2Half.negate().toTerm(intSort));
		final Term sub12Proof = res(theory.term(SMTLIBConstants.EQUALS, modNat, moddedValueTerm), modProof,
				mProofRules.cong(subTerm, sub2Term));
		final Term resultTerm = moddedValue.sub(pow2Half).toTerm(intSort);


		return res(theory.term(SMTLIBConstants.EQUALS, intbv, intbvnat),
				res(theory.term(SMTLIBConstants.EQUALS, bv, bvnat),
						mProofRules.bvConst(val, BigInteger.valueOf(bitLength)),
						mProofRules.cong(intbv, intbvnat)),
				res(theory.term(SMTLIBConstants.EQUALS, intbvnat, subTerm),
						mProofRules.int2sbv2int(BigInteger.valueOf(bitLength), nat),
						res(theory.term(SMTLIBConstants.EQUALS, subTerm, sub2Term), sub12Proof,
								res(theory.term(SMTLIBConstants.EQUALS, sub2Term, resultTerm),
										mProofRules.polyAdd(sub2Term, resultTerm),
										mProofRules.trans(intbv, intbvnat, subTerm, sub2Term, resultTerm)))));
	}

	/**
	 * Prove the equality between two int_to_bv terms provided there arguments are
	 * equal modulo pow2(bitlength). As a special case the second term can also be
	 * rewritten with the ubv2int2bv rule.
	 *
	 * @param bv1 the first int_to_bv term.
	 * @param bv2 the second int_to_bv term.
	 * @return the proof for `(= bv1 bv2)`.
	 */
	public Term proveInt2BvEquality(Term bv1, Term bv2) {
		final Theory theory = bv1.getTheory();
		assert isApplication(SMTLIBConstants.INT_TO_BV, bv1);

		final Term midTerm = isApplication(SMTLIBConstants.INT_TO_BV, bv2) ? bv2 :
				theory.term(((ApplicationTerm) bv1).getFunction(), theory.term(SMTLIBConstants.UBV_TO_INT, bv2));
		assert isApplication(SMTLIBConstants.INT_TO_BV, midTerm);
		if (bv1 == midTerm) {
			if (midTerm == bv2) {
				return mProofRules.refl(bv1);
			} else {
				return mProofRules.ubv2int2bv(bv2);
			}
		}
		final FunctionSymbol intToBv = ((ApplicationTerm) bv1).getFunction();
		final Term int1 = ((ApplicationTerm) bv1).getParameters()[0];
		final Term int2 = ((ApplicationTerm) midTerm).getParameters()[0];
		final BigInteger bitLength = new BigInteger(intToBv.getIndices()[0]);
		final Rational pow2 = Rational.valueOf(BigInteger.ONE.shiftLeft(bitLength.intValue()), BigInteger.ONE);
		final Term pow2Term = pow2.toTerm(int1.getSort());
		final Term mod1 = theory.term(SMTLIBConstants.MOD, int1, pow2Term);
		final Term mod2 = theory.term(SMTLIBConstants.MOD, int2, pow2Term);
		final Polynomial poly = new Polynomial(int2);
		poly.add(pow2.negate(), theory.term(SMTLIBConstants.DIV, int2, pow2Term));
		final Term modAsDiv2 = poly.toTerm(int2.getSort());
		final Term modProof1 = proveModNormalize(mod1, modAsDiv2);
		final Term modProof2 = res(theory.term(SMTLIBConstants.EQUALS, mod2, modAsDiv2),
				proveModNormalize(mod2, modAsDiv2), mProofRules.symm(modAsDiv2, mod2));
		final Term intbvint1 = theory.term(SMTLIBConstants.UBV_TO_INT, bv1);
		final Term intbvint2 = theory.term(SMTLIBConstants.UBV_TO_INT, midTerm);
		Term proof = res(theory.term(SMTLIBConstants.EQUALS, intbvint1, mod1), mProofRules.int2ubv2int(bitLength, int1),
				res(theory.term(SMTLIBConstants.EQUALS, mod1, modAsDiv2), modProof1, res(
						theory.term(SMTLIBConstants.EQUALS, modAsDiv2, mod2), modProof2,
						res(theory.term(SMTLIBConstants.EQUALS, mod2, intbvint2),
								res(theory.term(SMTLIBConstants.EQUALS, intbvint2, mod2),
										mProofRules.int2ubv2int(bitLength, int2), mProofRules.symm(mod2, intbvint2)),
								mProofRules.trans(intbvint1, mod1, modAsDiv2, mod2, intbvint2)))));
		final Term bvintbvint1 = theory.term(intToBv, intbvint1);
		final Term bvintbvint2 = theory.term(intToBv, intbvint2);
		proof = res(theory.term(SMTLIBConstants.EQUALS, intbvint1, intbvint2), proof,
				mProofRules.cong(bvintbvint1, bvintbvint2));
		proof = res(theory.term(SMTLIBConstants.EQUALS, bv1, bvintbvint1),
				res(theory.term(SMTLIBConstants.EQUALS, bvintbvint1, bv1), mProofRules.ubv2int2bv(bv1),
						mProofRules.symm(bv1, bvintbvint1)),
				res(theory.term(SMTLIBConstants.EQUALS, bvintbvint1, bvintbvint2), proof,
						res(theory.term(SMTLIBConstants.EQUALS, bvintbvint2, midTerm), mProofRules.ubv2int2bv(midTerm),
								mProofRules.trans(bv1, bvintbvint1, bvintbvint2, midTerm))));
		if (midTerm != bv2) {
			proof = proveTransitivity(bv1, midTerm, bv2, proof, mProofRules.ubv2int2bv(bv2));
		}
		return proof;
	}

	/**
	 * Prove the disequality between two distinct bitvector constant terms.
	 *
	 * @param bv1 the left-hand side of the equality
	 * @param bv2 the right-hand side of the equality
	 * @return the proof for `~(= bv1 bv2)` or null if this is not a trivial
	 *         disequality.
	 */
	public Term proveBitVecDisequality(final Term bv1, final Term bv2) {
		final Theory theory = bv1.getTheory();
		final BigInteger val1 = (BigInteger) ((ConstantTerm) bv1).getValue();
		final BigInteger val2 = (BigInteger) ((ConstantTerm) bv2).getValue();
		final Sort intSort = theory.getSort(SMTLIBConstants.INT);
		final Term nat1 = Rational.valueOf(val1, BigInteger.ONE).toTerm(intSort);
		final Term nat2 = Rational.valueOf(val2, BigInteger.ONE).toTerm(intSort);
		final Term intbv1 = theory.term(SMTLIBConstants.UBV_TO_INT, bv1);
		final Term intbv2 = theory.term(SMTLIBConstants.UBV_TO_INT, bv2);

		Term proof = res(theory.term(SMTLIBConstants.EQUALS, nat1, intbv1),
				res(theory.term(SMTLIBConstants.EQUALS, intbv1, nat1), proveUbvToIntConstant(bv1),
						mProofRules.symm(nat1, intbv1)),
				res(theory.term(SMTLIBConstants.EQUALS, intbv2, nat2), proveUbvToIntConstant(bv2),
						mProofRules.trans(nat1, intbv1, intbv2, nat2)));
		proof = res(theory.term(SMTLIBConstants.EQUALS, intbv1, intbv2), mProofRules.cong(intbv1, intbv2), proof);
		proof = res(theory.term(SMTLIBConstants.EQUALS, nat1, nat2), proof, proveTrivialDisequality(nat1, nat2));
		return proof;
	}

	/**
	 * Prove the disequality between two distinct constant datatype terms.
	 *
	 * @param dt1 the left-hand side of the equality
	 * @param dt2 the right-hand side of the equality
	 * @return the proof for `~(= dt1 dt2)`.
	 */
	public Term proveDTDisequality(final Term dt1, final Term dt2) {
		final Theory theory = dt1.getTheory();
		final ApplicationTerm dt1app = (ApplicationTerm) dt1;
		final ApplicationTerm dt2app = (ApplicationTerm) dt2;
		final DataType dt = (DataType) dt1.getSort().getSortSymbol();
		assert dt1 != dt2;
		assert dt1app.getFunction().isConstructor();
		assert dt2app.getFunction().isConstructor();
		final String consName1 = dt1app.getFunction().getName();
		if (dt1app.getFunction() != dt2app.getFunction()) {
			final FunctionSymbol tester =
					theory.getFunctionWithResult(SMTLIBConstants.IS, new String[] { consName1 }, null, dt1.getSort());
			final Term tester1 = theory.term(tester, dt1app);
			final Term tester2 = theory.term(tester, dt2app);
			final Term eqTesters = theory.term(SMTLIBConstants.EQUALS, tester1, tester2);
			return res(eqTesters,
				mProofRules.cong(tester1, tester2),
				res(tester1, mProofRules.dtTestI(dt1app),
						res(tester2, mProofRules.iffElim2(eqTesters),
									mProofRules.dtTestE(consName1, dt2app))));
		} else {
			final Term[] dt1args = dt1app.getParameters();
			final Term[] dt2args = dt2app.getParameters();
			for (int i = 0; i < dt1args.length; i++) {
				if (dt1args[i] != dt2args[i]) {
					final Constructor cons = dt.getConstructor(consName1);
					final FunctionSymbol selector = theory.getFunction(cons.getSelectors()[i], dt1app.getSort());
					final Term seldt1 = theory.term(selector, dt1);
					final Term seldt2 = theory.term(selector, dt2);
					final Term subproof = proveDTDisequality(dt1args[i], dt2args[i]);
					Term proof = res(theory.term(SMTLIBConstants.EQUALS, seldt1, seldt2),
							mProofRules.cong(seldt1, seldt2),
							res(theory.term(SMTLIBConstants.EQUALS, dt1args[i], dt2args[i]),
									mProofRules.trans(dt1args[i], seldt1, seldt2, dt2args[i]),
									subproof));
					proof = res(theory.term(SMTLIBConstants.EQUALS, seldt2, dt2args[i]),
							mProofRules.dtProject(seldt2), proof);
					proof = res(theory.term(SMTLIBConstants.EQUALS, seldt1, dt1args[i]), mProofRules.dtProject(seldt1),
							res(theory.term(SMTLIBConstants.EQUALS, dt1args[i], seldt1),
									mProofRules.symm(dt1args[i], seldt1), proof));
					return proof;
				}
			}
			throw new AssertionError("different data types with same arguments");
		}
	}

	/**
	 * Prove a select over store of const for constant arguments.
	 *
	 * @param term  the `select(store(...store(const v, ...)..., i, vi), ik)` term.
	 * @param value the value to which the select term evaluates to.
	 * @return the proof for `(= term value)`.
	 */
	public Term proveSelectOverStore(final Term term, final Term value) {
		final Theory theory = term.getTheory();
		ApplicationTerm selectTerm = (ApplicationTerm) term;
		final FunctionSymbol selectFunc = selectTerm.getFunction();
		Term array = selectTerm.getParameters()[0];
		final Term index = selectTerm.getParameters()[1];
		Term proof = null;
		while (isApplication(SMTLIBConstants.STORE, array)) {
			final Term[] storeArgs = ((ApplicationTerm) array).getParameters();
			if (storeArgs[1] == index) {
				assert storeArgs[2] == value;
				proof = res(theory.term(SMTLIBConstants.EQUALS, selectTerm, value),
						mProofRules.selectStore1(storeArgs[0], storeArgs[1], storeArgs[2]), proof);
				return proof;
			}
			final Term subSelectTerm = theory.term(selectFunc, storeArgs[0], index);
			proof = res(theory.term(SMTLIBConstants.EQUALS, selectTerm, value),
					res(theory.term(SMTLIBConstants.EQUALS, storeArgs[1], index),
							res(theory.term(SMTLIBConstants.EQUALS, selectTerm, subSelectTerm),
									mProofRules.selectStore2(array, index, value, index),
							mProofRules.trans(selectTerm, subSelectTerm, value)),
							proveDisequality(storeArgs[1], index)),
					proof);

			array = storeArgs[0];
			selectTerm = (ApplicationTerm) theory.term(selectFunc, array, index);
		}
		assert isApplication(SMTLIBConstants.CONST, array);
		return res(theory.term(SMTLIBConstants.EQUALS, selectTerm, value), mProofRules.constArray(value, index), proof);
	}

	/**
	 * Return the value stored in the given constant array at the given constant
	 * index.
	 *
	 * @param array the constant array term (store of store of const)
	 * @param index the constant index term.
	 * @return the constant value stored in the array.
	 */
	private Term evaluateSelect(Term array, Term index) {
		while (isApplication(SMTLIBConstants.STORE, array)) {
			final Term[] storeArgs = ((ApplicationTerm) array).getParameters();
			if (storeArgs[1] == index) {
				return storeArgs[2];
			}
			array = storeArgs[0];
		}
		if (isApplication(SMTLIBConstants.CONST, array)) {
			return ((ApplicationTerm) array).getParameters()[0];
		}
		throw new AssertionError("Not a valid array constant");
	}

	/**
	 * Return a (constant) index term where the two constant arrays differ.
	 *
	 * @param array1 the first constant array term (store of store of const)
	 * @param array2 the second constant array term.
	 * @return the constant index term where they differ.
	 */
	private Term findDistinctIndices(Term array1, Term array2) {
		while (isApplication(SMTLIBConstants.STORE, array1)) {
			final Term[] storeArgs = ((ApplicationTerm) array1).getParameters();
			if (storeArgs[2] == evaluateSelect(array2, storeArgs[1])) {
				return storeArgs[1];
			}
			array1 = storeArgs[0];
		}
		while (isApplication(SMTLIBConstants.STORE, array2)) {
			final Term[] storeArgs = ((ApplicationTerm) array2).getParameters();
			if (storeArgs[2] == evaluateSelect(array1, storeArgs[1])) {
				return storeArgs[1];
			}
			array2 = storeArgs[0];
		}
		// two const arrays. They differ on any "fresh" index
		throw new AssertionError("Fresh Index not yet implemented");
	}

	/**
	 * Prove the disequality between two distinct constant array terms.
	 *
	 * @param arr1 the left-hand side of the equality
	 * @param arr2 the right-hand side of the equality
	 * @return the proof for `~(= arr1 arr2)`.
	 */
	public Term proveArrayDisequality(final Term arr1, final Term arr2) {
		// First we determine the index where arr1 and arr2 differ.
		final Theory theory = arr1.getTheory();
		final Term index = findDistinctIndices(arr1, arr2);
		final Term val1 = evaluateSelect(arr1, index);
		final Term val2 = evaluateSelect(arr2, index);
		assert val1 != val2;
		final Term sel1 = theory.term(SMTLIBConstants.SELECT, arr1, index);
		final Term sel2 = theory.term(SMTLIBConstants.SELECT, arr2, index);
		final Term val1Eq = proveSelectOverStore(sel1, val1);
		final Term val2Eq = proveSelectOverStore(sel2, val2);
		final Term eqSelect = theory.term(SMTLIBConstants.EQUALS, sel1, sel2);
		return res(eqSelect,
				res(theory.term(SMTLIBConstants.EQUALS, index, index),
						mProofRules.refl(index),
						mProofRules.cong(sel1, sel2)),
				res(theory.term(SMTLIBConstants.EQUALS, val1, val2),
						res(theory.term(SMTLIBConstants.EQUALS, sel2, val2), val2Eq,
								res(theory.term(SMTLIBConstants.EQUALS, val1, sel1),
										res(theory.term(SMTLIBConstants.EQUALS, sel1, val1), val1Eq,
												mProofRules.symm(val1, sel1)),
						mProofRules.trans(val1, sel1, sel2, val2))),
						proveDisequality(val1, val2)));
	}

	/**
	 * Prove the disequality between two distinct constant terms in normalized form.
	 *
	 * @param t1 the left-hand side of the equality
	 * @param t2 the right-hand side of the equality
	 * @return the proof for `~(= t1 t2)` or null if this is not a trivial
	 *         disequality.
	 */
	public Term proveDisequality(final Term t1, final Term t2) {
		final Sort sort = t1.getSort();
		if (sort.isNumericSort()) {
			return proveTrivialDisequality(t1, t2);
		} else if (sort.isBitVecSort()) {
			return proveBitVecDisequality(t1, t2);
		} else if (sort.isArraySort()) {
			return proveArrayDisequality(t1, t2);
		} else if (sort.getSortSymbol().isDatatype()) {
			return proveDTDisequality(t1, t2);
		} else {
			// TODO: Do we want model value disequalities? Or do we make them datatypes?
			final Theory theory = t1.getTheory();
			return mProofRules.oracle(
					new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, t1, t2), false) },
					new Annotation[] { new Annotation(":trivialdiseq", null) });
		}
	}

	/**
	 * Prove (= t1 t3) from (= t1 t2) and (= t2 t3).
	 *
	 * @param t1        first term.
	 * @param t2        second term.
	 * @param t3        third term.
	 * @param prooft1t2 proof of (= t1 t2).
	 * @param prooft2t3 proof of (= t2 t3).
	 * @return proof of (= t1 t3).
	 */
	public Term proveTransitivity(Term t1, Term t2, Term t3, Term prooft1t2, Term prooft2t3) {
		if (t1 == t2) {
			return prooft2t3;
		}
		if (t2 == t3) {
			return prooft1t2;
		}
		final Theory theory = t1.getTheory();
		return res(theory.term(SMTLIBConstants.EQUALS, t1, t2), prooft1t2,
				res(theory.term(SMTLIBConstants.EQUALS, t2, t3), prooft2t3, mProofRules.trans(t1, t2, t3)));
	}
}
