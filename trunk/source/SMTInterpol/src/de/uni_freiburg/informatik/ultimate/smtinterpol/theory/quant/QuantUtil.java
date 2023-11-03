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
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermCompiler;

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
				for (Term arg : appTerm.getParameters()) {
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
				final SMTAffineTerm affineTerm = SMTAffineTerm.create(term);
				for (Term summand : affineTerm.getSummands().keySet()) {
					if (!isEssentiallyUninterpreted(summand)) {
						return false;
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
			final SMTAffineTerm lhsAff = new SMTAffineTerm(eq.getLhs());
			if (containsArithmeticOnQuantOnlyAtTopLevel(lhsAff)) {
				final SMTAffineTerm rhsAff = new SMTAffineTerm(eq.getRhs());
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
			final SMTAffineTerm lhsAff = new SMTAffineTerm(lhs);
			final SMTAffineTerm rhsAff = new SMTAffineTerm(rhs);
			allSummandsWithoutCoeffs.addAll(lhsAff.getSummands().keySet());
			allSummandsWithoutCoeffs.addAll(rhsAff.getSummands().keySet());
		} else {
			final QuantBoundConstraint bc = (QuantBoundConstraint) atom;
			allSummandsWithoutCoeffs.addAll(bc.getAffineTerm().getSummands().keySet());
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
			SMTAffineTerm remainder = new SMTAffineTerm();
			SMTAffineTerm aff = bc.getAffineTerm();
			for (final Entry<Term, Rational> smd : aff.getSummands().entrySet()) {
				if (smd.getKey() instanceof TermVariable) {
					if (smd.getValue().signum() < 0) {
						assert t1 == null;
						lowerVar = (TermVariable) smd.getKey();
					} else {
						assert upperVar == null;
						upperVar = (TermVariable) smd.getKey();
					}
				} else {
					remainder.add(smd.getValue(), smd.getKey());
				}
			}
			remainder.add(aff.getConstant());
			assert lowerVar != null || upperVar != null;
			if (lowerVar != null && upperVar != null) {
				assert remainder.isConstant() && remainder.getConstant() == Rational.ZERO;
				t1 = lowerVar;
				t2 = upperVar;
			} else if (lowerVar != null) {
				t1 = lowerVar;
				t2 = remainder.toTerm(compiler, lowerVar.getSort());
			} else {
				remainder.negate();
				t1 = remainder.toTerm(compiler, upperVar.getSort());
				t2 = upperVar;
			}
		}
		return new Term[] { t1, t2 };
	}

	/**
	 * Check if an affine term contains arithmetic on quantified terms only at top level, i.e., its summands do not
	 * contain arithmetic on quantified terms.
	 * 
	 * @param at
	 *            the SMTAffineTerm to check
	 */
	public static boolean containsArithmeticOnQuantOnlyAtTopLevel(final SMTAffineTerm at) {
		for (final Term smd : at.getSummands().keySet()) {
			if (!(smd instanceof TermVariable) && !isSimpleEU(smd)) {
				return false;
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
			FunctionSymbol fsym = ((ApplicationTerm) term).getFunction();
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
			FunctionSymbol fsym = ((ApplicationTerm) term).getFunction();
			return fsym.isIntern() && fsym.getName().startsWith("@0");
		}
		return false;
	}
}
