/*
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute;

import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.DIVIDE;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.EQUALS;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.GEQ;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.GT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.INT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.LEQ;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.LT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.MINUS;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.MUL;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.PLUS;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.TO_INT;
import static de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants.TO_REAL;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

/**
 * Proof rules for arithmetic.
 */
public class ArithmeticRules {

	public static void registerRules(MinimalProofChecker checker) {
		checker.registerExpand(MINUS, ArithmeticRules::expandMinus);
		checker.registerExpand(GT, ArithmeticRules::expandGt);
		checker.registerExpand(GEQ, ArithmeticRules::expandGeq);

		checker.registerAxiom(ProofRules.TRICHOTOMY, ArithmeticRules::trichotomy);
		checker.registerAxiom(ProofRules.TOTAL, ArithmeticRules::total);
		checker.registerAxiom(ProofRules.TOTALINT, ArithmeticRules::totalInt);
		checker.registerAxiom(ProofRules.FARKAS, ArithmeticRules::farkas);
		checker.registerAxiom(ProofRules.MULPOS, ArithmeticRules::mulPos);
		checker.registerAxiom(ProofRules.POLYADD, ArithmeticRules::polyAdd);
		checker.registerAxiom(ProofRules.POLYMUL, ArithmeticRules::polyMul);
		checker.registerAxiom(ProofRules.TOREALDEF, ArithmeticRules::toRealDef);
		checker.registerAxiom(ProofRules.DIVIDEDEF, ArithmeticRules::divideDef);
		checker.registerAxiom(ProofRules.TOINTLOW, ArithmeticRules::toIntLow);
		checker.registerAxiom(ProofRules.TOINTHIGH, ArithmeticRules::toIntHigh);
		checker.registerAxiom(ProofRules.DIVLOW, ArithmeticRules::divLow);
		checker.registerAxiom(ProofRules.DIVHIGH, ArithmeticRules::divHigh);
		checker.registerAxiom(ProofRules.MODDEF, ArithmeticRules::modDef);
	}

	public static Term expandMinus(FunctionSymbol f, Term[] params) {
		assert f.getName() == MINUS && params.length <= 2;
		assert params.length == 1 || params[0].getSort() == params[1].getSort();
		final Theory t = params[0].getTheory();
		final Term mone = Rational.MONE.toTerm(params[0].getSort());
		return params.length == 1 ? t.term(MUL, mone, params[0])
				: t.term(PLUS, params[0], t.term(MUL, mone, params[1]));
	}

	public static Term expandGt(FunctionSymbol f, Term[] params) {
		assert f.getName() == GT && params.length == 2;
		final Theory t = params[0].getTheory();
		return t.term(LT, params[1], params[0]);
	}

	public static Term expandGeq(FunctionSymbol f, Term[] params) {
		assert f.getName() == GEQ && params.length == 2;
		final Theory t = params[0].getTheory();
		return t.term(LEQ, params[1], params[0]);
	}

	public static ProofLiteral[] trichotomy(MinimalProofChecker checker, Theory theory, Object[] params) {
		final Term[] args = (Term[]) params;
		return new ProofLiteral[] { new ProofLiteral(theory.term(LT, args), true),
				new ProofLiteral(theory.term(EQUALS, args), true),
				new ProofLiteral(theory.term(LT, args[1], args[0]), true) };
	}

	public static ProofLiteral[] total(MinimalProofChecker checker, Theory theory, Object[] params) {
		final Term[] args = (Term[]) params;
		return new ProofLiteral[] { new ProofLiteral(theory.term(LEQ, args[0], args[1]), true),
				new ProofLiteral(theory.term(LT, args[1], args[0]), true) };

	}

	public static ProofLiteral[] totalInt(MinimalProofChecker checker, Theory theory, Object[] params) {
		final Term x = (Term) params[0];
		final Term cTerm = (Term) params[1];
		final Rational c = (Rational) ((ConstantTerm) cTerm).getValue();
		if (!x.getSort().getName().equals(INT) || cTerm.getSort() != x.getSort()
				|| !c.denominator().equals(BigInteger.ONE)) {
			throw new IllegalArgumentException("total-int: x must be Int, c integer constant of same sort");
		}
		final Term cPlusOne = c.add(Rational.ONE).toTerm(x.getSort());
		return new ProofLiteral[] { new ProofLiteral(theory.term(LEQ, x, cTerm), true),
				new ProofLiteral(theory.term(LEQ, cPlusOne, x), true) };
	}

	public static ProofLiteral[] farkas(MinimalProofChecker checker, Theory theory, Object[] params) {
		if (!ArithmeticRules.checkFarkas(params)) {
			throw new IllegalArgumentException("Side condition violated");
		}
		final HashSet<ProofLiteral> clause = new HashSet<>();
		for (int i = 1; i < params.length; i += 2) {
			clause.add(new ProofLiteral((Term) params[i], false));
		}
		return clause.toArray(new ProofLiteral[clause.size()]);
	}

	public static ProofLiteral[] mulPos(MinimalProofChecker checker, Theory theory, Object[] params) {
		final Term[] ineqs = (Term[]) params;
		if (!ArithmeticRules.checkMulPos(ineqs)) {
			throw new IllegalArgumentException("Side condition violated");
		}
		final HashSet<ProofLiteral> clause = new HashSet<>();
		for (int i = 0; i < ineqs.length; i++) {
			clause.add(new ProofLiteral(ineqs[i], i == ineqs.length - 1));
		}
		return clause.toArray(new ProofLiteral[clause.size()]);
	}

	public static ProofLiteral[] polyAdd(MinimalProofChecker checker, Theory theory, Object[] axParams) {
		final Term[] params = (Term[]) axParams;
		assert params.length == 2;
		if (!ArithmeticRules.checkPolyAdd(params[0], params[1])) {
			throw new IllegalArgumentException("Side condition violated");
		}
		return new ProofLiteral[] { new ProofLiteral(theory.term(EQUALS, params[0], params[1]), true) };
	}

	public static ProofLiteral[] polyMul(MinimalProofChecker checker, Theory theory, Object[] axParams) {
		final Term[] params = (Term[]) axParams;
		assert params.length == 2;
		if (!ArithmeticRules.checkPolyMul(params[0], params[1])) {
			throw new IllegalArgumentException("Side condition violated");
		}
		return new ProofLiteral[] { new ProofLiteral(theory.term(EQUALS, params[0], params[1]), true) };
	}

	public static ProofLiteral[] toRealDef(MinimalProofChecker checker, Theory theory, Object[] params) {
		assert params.length == 1;
		final Term integerTerm = (Term) params[0];
		final Term lhs = theory.term(TO_REAL, integerTerm);
		final Term rhs = ArithmeticRules.computePolyToReal(integerTerm);
		return new ProofLiteral[] { new ProofLiteral(theory.term(EQUALS, lhs, rhs), true) };
	}

	public static ProofLiteral[] divideDef(MinimalProofChecker checker, Theory theory, Object[] axParams) {
		final Term[] divParams = (Term[]) axParams;
		assert divParams.length >= 2;
		final Term divide = theory.term(DIVIDE, divParams);
		final Term[] mulParams = new Term[divParams.length];
		System.arraycopy(divParams, 1, mulParams, 0, divParams.length - 1);
		mulParams[divParams.length - 1] = divide;
		final Term lhs = theory.term(MUL, mulParams);
		final LinkedHashSet<ProofLiteral> clause = new LinkedHashSet<>();
		clause.add(new ProofLiteral(theory.term(EQUALS, lhs, divParams[0]), true));
		for (int i = 1; i < divParams.length; i++) {
			clause.add(new ProofLiteral(
					theory.term(EQUALS, divParams[i], Rational.ZERO.toTerm(divParams[i].getSort())),
					true));
		}
		return clause.toArray(new ProofLiteral[clause.size()]);
	}

	public static ProofLiteral[] toIntLow(MinimalProofChecker checker, Theory theory, Object[] axParams) {
		assert axParams.length == 1;
		final Term arg = (Term) axParams[0];
		final Term toRealToInt = theory.term(TO_REAL, theory.term(TO_INT, arg));
		return new ProofLiteral[] { new ProofLiteral(theory.term(LEQ, toRealToInt, arg), true) };
	}

	public static ProofLiteral[] toIntHigh(MinimalProofChecker checker, Theory theory, Object[] axParams) {
		assert axParams.length == 1;
		final Term arg = (Term) axParams[0];
		final Term toRealToInt = theory.term(TO_REAL, theory.term(TO_INT, arg));
		final Term toRealPlusOne = theory.term(PLUS, toRealToInt, Rational.ONE.toTerm(arg.getSort()));
		return new ProofLiteral[] { new ProofLiteral(theory.term(LT, arg, toRealPlusOne), true) };
	}

	public static ProofLiteral[] divLow(MinimalProofChecker checker, Theory theory, Object[] axParams) {
		final Term[] params = (Term[]) axParams;
		assert params.length == 2;
		final Term arg = params[0];
		final Term divisor = params[1];
		final Term divTerm = theory.term(SMTLIBConstants.DIV, arg, divisor);
		final Term mulDivTerm = theory.term(SMTLIBConstants.MUL, divisor, divTerm);
		final Term zero = Rational.ZERO.toTerm(divisor.getSort());
		return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.LEQ, mulDivTerm, arg), true),
				new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, divisor, zero), true) };
	}

	public static ProofLiteral[] divHigh(MinimalProofChecker checker, Theory theory, Object[] axParams) {
		final Term[] params = (Term[]) axParams;
		assert params.length == 2;
		final Term arg = params[0];
		final Term divisor = params[1];
		final Term divTerm = theory.term(SMTLIBConstants.DIV, arg, divisor);
		final Term mulDivTerm = theory.term(SMTLIBConstants.MUL, divisor, divTerm);
		final Term mulDivTermPlus = theory.term(SMTLIBConstants.PLUS, mulDivTerm,
				theory.term(SMTLIBConstants.ABS, divisor));
		final Term zero = Rational.ZERO.toTerm(divisor.getSort());
		return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.LT, arg, mulDivTermPlus), true),
				new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, divisor, zero), true) };
	}

	public static ProofLiteral[] modDef(MinimalProofChecker checker, Theory theory, Object[] axParams) {
		final Term[] params = (Term[]) axParams;
		assert params.length == 2;
		final Term arg = params[0];
		final Term divisor = params[1];
		final Term divTerm = theory.term(SMTLIBConstants.DIV, arg, divisor);
		final Term mulDivTerm = theory.term(SMTLIBConstants.MUL, divisor, divTerm);
		final Term modTerm = theory.term(SMTLIBConstants.MOD, arg, divisor);
		final Term modDef = theory.term(SMTLIBConstants.PLUS, mulDivTerm, modTerm);
		final Term zero = Rational.ZERO.toTerm(divisor.getSort());
		return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, modDef, arg), true),
				new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, divisor, zero), true) };
	}

	public static boolean checkFarkas(final Object[] params) {
		if (params.length % 2 != 0 || params.length < 2) {
			return false;
		}
		final Polynomial sum = new Polynomial();
		boolean strict = false;
		for (int i = 0; i < params.length; i+=2) {
			final BigInteger coeff = (BigInteger) params[i];
			final Term ineq = (Term) params[i + 1];
			if (coeff.signum() != 1) {
				return false;
			}
			if (ProofRules.isApplication(LT, ineq)) {
				strict = true;
			} else if (!ProofRules.isApplication(LEQ, ineq) && !ProofRules.isApplication(EQUALS, ineq)) {
				return false;
			}
			final ApplicationTerm appTerm = (ApplicationTerm) ineq;
			final Term[] polys = appTerm.getParameters();
			if (polys.length != 2) {
				return false;
			}
			final Rational coeffRat = Rational.valueOf(coeff, BigInteger.ONE);
			sum.add(coeffRat, polys[0]);
			sum.add(coeffRat.negate(), polys[1]);
		}
		final boolean okay = sum.isConstant() && sum.getConstant().signum() >= (strict ? 0 : 1);
		return okay;
	}

	public static boolean checkMulPos(final Term[] inequalities) {
		final Polynomial prod = new Polynomial();
		prod.add(Rational.ONE);
		boolean holdsStrictly = true;
		for (int i = 0; i < inequalities.length; i++) {
			if (ProofRules.isApplication(LEQ, inequalities[i])) {
				holdsStrictly = false;
			} else if (!ProofRules.isApplication(LT, inequalities[i])) {
				return false;
			}
			final ApplicationTerm appTerm = (ApplicationTerm) inequalities[i];
			final Term[] params = appTerm.getParameters();
			if (params.length != 2) {
				return false;
			}
			if (params[0] != Rational.ZERO.toTerm(params[0].getSort())) {
				return false;
			}
			if (i < inequalities.length - 1) {
				prod.mul(new Polynomial(params[1]));
			} else {
				if (!holdsStrictly && !ProofRules.isApplication(LEQ, inequalities[i])) {
					return false;
				}
				prod.add(Rational.MONE, params[1]);
			}
		}
		return prod.isZero();
	}

	private static Term computeFactorToReal(final Term factor) {
		if (factor instanceof ConstantTerm && ((ConstantTerm) factor).getValue() instanceof Rational) {
			return ((Rational) ((ConstantTerm) factor).getValue()).toTerm(factor.getTheory().getSort("Real"));
		} else {
			return factor.getTheory().term(TO_REAL, factor);
		}
	}

	private static Term computeMonomialToReal(final Term monomial) {
		if (ProofRules.isApplication(MUL, monomial)) {
			final Term[] oldParams = ((ApplicationTerm) monomial).getParameters();
			final Term[] newParams = new Term[oldParams.length];
			for (int i = 0; i < oldParams.length; i++) {
				newParams[i] = ArithmeticRules.computeFactorToReal(oldParams[i]);
			}
			return monomial.getTheory().term(MUL, newParams);
		} else {
			return ArithmeticRules.computeFactorToReal(monomial);
		}
	}

	public static Term computePolyToReal(final Term poly) {
		if (ProofRules.isApplication(PLUS, poly)) {
			final Term[] oldParams = ((ApplicationTerm) poly).getParameters();
			final Term[] newParams = new Term[oldParams.length];
			for (int i = 0; i < oldParams.length; i++) {
				newParams[i] = ArithmeticRules.computeMonomialToReal(oldParams[i]);
			}
			return poly.getTheory().term(PLUS, newParams);
		} else {
			return ArithmeticRules.computeMonomialToReal(poly);
		}
	}

	/**
	 * Check the parameters of a poly* axiom. It checks that the mulTerm is an
	 * application of `*` and that the product of its arguments minus the results
	 * (using polynomial multiplication and subtraction) gives zero.
	 *
	 * @param mulTerm
	 *            the mul term (first argument of the poly* axiom).
	 * @param result
	 *            the result term (second argument of the poly* axiom).
	 * @return true iff the parameters are wellformed.
	 */
	public static boolean checkPolyMul(final Term mulTerm, final Term result) {
		if (!ProofRules.isApplication(MUL, mulTerm)) {
			return false;
		}
		final Polynomial poly = new Polynomial();
		poly.add(Rational.ONE);
		for (final Term t : ((ApplicationTerm) mulTerm).getParameters()) {
			poly.mul(new Polynomial(t));
		}
		poly.add(Rational.MONE, result);
		return poly.isZero();
	}

	/**
	 * Check the parameters of a poly+ axiom. It checks that the plusTerm is an
	 * application of `+` and that the sum of its arguments minus the results (using
	 * polynomial addition) sums to zero.
	 *
	 * @param plusTerm
	 *            the plus term (first argument of the poly+ axiom).
	 * @param result
	 *            the result term (second argument of the poly+ axiom).
	 * @return true iff the parameters are wellformed.
	 */
	public static boolean checkPolyAdd(final Term plusTerm, final Term result) {
		if (!ProofRules.isApplication(PLUS, plusTerm)) {
			return false;
		}
		final Polynomial poly = new Polynomial();
		for (final Term t : ((ApplicationTerm) plusTerm).getParameters()) {
			poly.add(Rational.ONE, t);
		}
		poly.add(Rational.MONE, result);
		return poly.isZero();
	}

}
