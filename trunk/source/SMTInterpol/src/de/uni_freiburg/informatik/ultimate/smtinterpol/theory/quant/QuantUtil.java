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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermCompiler;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

/**
 * This class contains helper methods to classify quantified terms and literals.
 *
 * @author Tanja Schindler
 */
public class QuantUtil {

	private QuantUtil() {
		// Not meant to be instantiated
	}

	/**
	 * Check if a given term is essentially uninterpreted, i.e., it is ground or variables only appear as arguments of
	 * uninterpreted functions.
	 *
	 * TODO Nonrecursive.
	 *
	 * @param term
	 *            The term to check.
	 * @return true if the term is essentially uninterpreted, false otherwise.
	 */
	public static boolean isEssentiallyUninterpreted(final Term term) {
		if (term.getFreeVars().length == 0) {
			return true;
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol func = appTerm.getFunction();
			if (!func.isInterpreted()) {
				for (final Term arg : appTerm.getParameters()) {
					if (!(arg instanceof TermVariable)) {
						if (!isEssentiallyUninterpreted(arg)) {
							return false;
						}
					}
				}
				return true;
			} else if (func.getName() == "select") {
				final Term[] params = appTerm.getParameters();
				if (params[0] instanceof TermVariable || !isEssentiallyUninterpreted(params[0])) {
					return false; // Quantified arrays are not allowed.
				}
				if (!(params[1] instanceof TermVariable) && !isEssentiallyUninterpreted(params[1])) {
					return false;
				}
				return true;
			} else if (func.getName() == "+" || func.getName() == "-" || func.getName() == "*") {
				final Polynomial affineTerm = new Polynomial(term);
				for (final Map<Term, Integer> summand : affineTerm.getSummands().keySet()) {
					for (final Term factor : summand.keySet()) {
						if (!isEssentiallyUninterpreted(factor)) {
							return false;
						}
					}
				}
				return true;
			} else {
				return false;
			}
		} else {
			return false;
		}
	}

	/**
	 * Check if a quantified atom contains arithmetic on quantified terms only at top level, i.e., the left and right
	 * hand side of the (in)equality are affine terms where the summands do not contain arithmetic on quantified terms
	 * themselves.
	 *
	 * @param atom
	 *            the quantified atom.
	 * @return true if the literal contains arithmetic on quantified terms only at top level, false else.
	 */
	public static boolean containsArithmeticOnQuantOnlyAtTopLevel(final QuantLiteral atom) {
		assert !atom.isNegated();
		if (atom instanceof QuantBoundConstraint) {
			return containsArithmeticOnQuantOnlyAtTopLevel(((QuantBoundConstraint) atom).getAffineTerm());
		} else {
			final QuantEquality eq = (QuantEquality) atom;
			final Polynomial lhsAff = new Polynomial(eq.getLhs());
			if (containsArithmeticOnQuantOnlyAtTopLevel(lhsAff)) {
				final Polynomial rhsAff = new Polynomial(eq.getRhs());
				return containsArithmeticOnQuantOnlyAtTopLevel(rhsAff);
			}
		}
		return false;
	}

	/**
	 * Check that any variable occurring in a quantified literal appears at least once in a function application within
	 * this literal, excluding top level arithmetic function applications.
	 *
	 * @param atom
	 *            the quantified atom.
	 * @return true if each variable appears at least once in a function application, false else.
	 * @see QuantUtil.containsArithmeticOnlyAtTopLevel(final QuantLiteral atom) for top level arithmetic.
	 */
	public static boolean containsAppTermsForEachVar(final QuantLiteral atom) {
		assert !atom.isNegated();
		final Set<Term> allSummandsWithoutCoeffs = new HashSet<>();
		if (atom instanceof QuantEquality) {
			final QuantEquality eq = (QuantEquality) atom;
			final Term lhs = eq.getLhs();
			final Term rhs = eq.getRhs();
			final Polynomial lhsAff = new Polynomial(lhs);
			final Polynomial rhsAff = new Polynomial(rhs);
			for (final Map<Term, Integer> monom : lhsAff.getSummands().keySet()) {
				allSummandsWithoutCoeffs.addAll(monom.keySet());
			}
			for (final Map<Term, Integer> monom : rhsAff.getSummands().keySet()) {
				allSummandsWithoutCoeffs.addAll(monom.keySet());
			}
		} else {
			final QuantBoundConstraint bc = (QuantBoundConstraint) atom;
			for (final Map<Term, Integer> monom : bc.getAffineTerm().getSummands().keySet()) {
				allSummandsWithoutCoeffs.addAll(monom.keySet());
			}
		}
		final Set<Term> varTerms = new HashSet<>();
		final Set<TermVariable> varsInApps = new HashSet<>();
		for (final Term smd : allSummandsWithoutCoeffs) {
			if (smd instanceof TermVariable) {
				varTerms.add(smd);
			} else if (smd.getFreeVars().length != 0) {
				varsInApps.addAll(Arrays.asList(smd.getFreeVars()));
			}
		}
		varTerms.removeAll(varsInApps);
		return varTerms.isEmpty();
	}

	/**
	 * Check if a quantified atom is an equality between two variables.
	 * @param atom the QuantLiteral atom
	 * @return true if the atom is an equality between two variables, false else.
	 */
	public static boolean isVarEq(final QuantLiteral atom) {
		assert !atom.isNegated();
		if (atom instanceof QuantEquality) {
			final QuantEquality eq = (QuantEquality) atom;
			return eq.getLhs() instanceof TermVariable && eq.getRhs() instanceof TermVariable;
		}
		return false;
	}

	/**
	 * For an arithmetical literal, get the terms t1, t2, such that the literal t1<t2 has form var<ground, ground<var,
	 * var<var, or t1=t2 has form var=ground.
	 *
	 * @param arithLit
	 *            an arithmetical literal
	 * @return the array [t1,t2]
	 */
	public static Term[] getArithmeticalTermLtTerm(final QuantLiteral arithLit, final TermCompiler compiler) {
		assert arithLit.isArithmetical();
		Term t1 = null;
		Term t2 = null;
		if (arithLit instanceof QuantEquality) {
			final QuantEquality eq = (QuantEquality) arithLit;
			assert eq.getLhs() instanceof TermVariable && eq.getRhs().getFreeVars().length == 0;
			t1 = eq.getLhs();
			t2 = eq.getRhs();
		} else {
			assert arithLit.isNegated();
			final QuantBoundConstraint bc = (QuantBoundConstraint) arithLit.getAtom();
			TermVariable lowerVar = null;
			TermVariable upperVar = null;
			final Polynomial remainder = new Polynomial();
			final Polynomial aff = bc.getAffineTerm();
			for (final Entry<Map<Term, Integer>, Rational> smd : aff.getSummands().entrySet()) {
				Term singleton = null;
				if (smd.getKey().size() == 1 && smd.getKey().values().iterator().next() == 1) {
					singleton = smd.getKey().keySet().iterator().next();
				}
				if (singleton instanceof TermVariable) {
					if (smd.getValue().signum() < 0) {
						assert t1 == null;
						lowerVar = (TermVariable) singleton;
					} else {
						assert upperVar == null;
						upperVar = (TermVariable) singleton;
					}
				} else {
					remainder.add(smd.getValue(), smd.getKey());
				}
			}
			assert lowerVar != null || upperVar != null;
			if (lowerVar != null && upperVar != null) {
				assert remainder.isZero();
				t1 = lowerVar;
				t2 = upperVar;
			} else if (lowerVar != null) {
				t1 = lowerVar;
				t2 = remainder.toTerm(lowerVar.getSort());
			} else {
				remainder.mul(Rational.MONE);
				t1 = remainder.toTerm(upperVar.getSort());
				t2 = upperVar;
			}
		}
		return new Term[] { t1, t2 };
	}

	public static boolean isTermVariable(Map<Term, Integer> monom) {
		return monom.size() == 1 &&
				monom.values().iterator().next() == 1 &&
				monom.keySet().iterator().next() instanceof TermVariable;
	}

	/**
	 * Check if an affine term contains arithmetic on quantified terms only at top level, i.e., its summands do not
	 * contain arithmetic on quantified terms.
	 *
	 * @param at
	 *            the SMTAffineTerm to check
	 */
	public static boolean containsArithmeticOnQuantOnlyAtTopLevel(final Polynomial at) {
		for (final Map<Term,Integer> monom : at.getSummands().keySet()) {
			if (!isTermVariable(monom)) {
				for (final Term factor : monom.keySet()) {
					if (!isSimpleEU(factor)) {
						return false;
					}
				}
			}
		}
		return true;
	}

	/**
	 * Check if a term is a "simple" EU term, i.e., it is ground, or an application of an uninterpreted function where
	 * all arguments are variables or simple EU terms. (Exception: select behaves as an uninterpreted function but may
	 * not have a variable as first argument.)
	 *
	 * TODO Nonrecursive.
	 *
	 * @param term
	 *            the term to check.
	 * @return true, if the term is a "simple" EU term, false otherwise.
	 */
	public static boolean isSimpleEU(final Term term) {
		if (term.getFreeVars().length != 0) {
			if (term instanceof TermVariable) {
				return false;
			} else {
				assert term instanceof ApplicationTerm;
				final ApplicationTerm at = (ApplicationTerm) term;
				final FunctionSymbol func = at.getFunction();
				if (func.isInterpreted() && !func.getName().equals("select")) {
					return false;
				}
				final Term[] args = at.getParameters();
				if (func.getName().equals("select")) {
					if (!isSimpleEU(args[0])) {
						return false; // Quantified arrays are not allowed.
					}
					if (!(args[1] instanceof TermVariable) && !isSimpleEU(args[1])) {
						return false;
					}
				} else {
					for (final Term arg : args) {
						if (!(arg instanceof TermVariable) && !isSimpleEU(arg)) {
							return false;
						}
					}
				}
			}
		}
		return true;
	}

	/**
	 * Check if a term is an application term with an internal {@literal @}AUX function.
	 *
	 * @param term
	 *            the term to check.
	 */
	public static boolean isAuxApplication(final Term term) {
		if (term instanceof ApplicationTerm) {
			final FunctionSymbol fsym = ((ApplicationTerm) term).getFunction();
			return fsym.isIntern() && fsym.getName().startsWith("@AUX");
		}
		return false;
	}

	/**
	 * Check if a term is a lambda.
	 *
	 * @param term
	 *            the term to check.
	 */
	public static boolean isLambda(final Term term) {
		if (term instanceof ApplicationTerm) {
			final FunctionSymbol fsym = ((ApplicationTerm) term).getFunction();
			return fsym.isIntern() && fsym.getName().startsWith("@0");
		}
		return false;
	}
}
