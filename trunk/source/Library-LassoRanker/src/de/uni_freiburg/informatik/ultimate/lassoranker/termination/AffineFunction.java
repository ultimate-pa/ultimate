/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.termination;

import java.io.Serializable;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents an affine-linear function of the from
 *
 * <pre>
 * f(x) = Σ c_i * x_i + b
 * </pre>
 *
 * with a vector c_1, ... c_n and a constant b.
 *
 * This is similar to the class LinearInequality, but serves a different purpose. The coefficients are restricted to
 * integers and the variables are Boogie variables.
 *
 * This will be generated and administered by the AffineFunctionGenerator class. It generates parameters whose solution
 * gives rise to this affine function instance.
 *
 * The purpose of this class is to serve as a foundation to ranking functions and supporting invariants.
 *
 * @author Jan Leike
 */
public class AffineFunction implements Serializable {
	private static final long serialVersionUID = -3142354398708751882L;

	protected final Map<IProgramVar, BigInteger> mCoefficients;
	protected BigInteger mConstant;

	public AffineFunction() {
		mCoefficients = new LinkedHashMap<IProgramVar, BigInteger>();
		mConstant = BigInteger.ZERO;
	}

	/**
	 * @return whether this function is a constant function
	 */
	public boolean isConstant() {
		return mCoefficients.isEmpty();
	}

	/**
	 * @return the constant
	 */
	public BigInteger getConstant() {
		return mConstant;
	}

	/**
	 * @param c
	 *            set the constant to c
	 */
	public void setConstant(final BigInteger c) {
		mConstant = c;
	}

	/**
	 * @return the set of RankVar's that occur in this function
	 */
	public Set<IProgramVar> getVariables() {
		return mCoefficients.keySet();
	}

	// /**
	// * @return the set of (associated) BoogieVar's that occur in this function
	// */
	// public Set<BoogieVar> getBoogieVariables() {
	// Set<BoogieVar> result = new LinkedHashSet<BoogieVar>();
	// for (RankVar rkVar : mcoefficients.keySet()) {
	// BoogieVar boogieVar = rkVar.getAssociatedBoogieVar();
	// if (boogieVar != null) {
	// result.add(boogieVar);
	// }
	// }
	// return result;
	// }

	/**
	 * @param var
	 *            a RankVar variable
	 * @return the coefficient of to this variable
	 */
	public BigInteger get(final IProgramVar var) {
		return mCoefficients.get(var);
	}

	/**
	 * Set the coefficient to a variable
	 *
	 * @param var
	 *            a Boogie variable
	 * @param coeff
	 *            the coefficient of this variable
	 */
	public void put(final IProgramVar var, final BigInteger coeff) {
		if (coeff.equals(BigInteger.ZERO)) {
			mCoefficients.remove(var);
		} else {
			mCoefficients.put(var, coeff);
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		boolean first = true;
		for (final Map.Entry<IProgramVar, BigInteger> entry : mCoefficients.entrySet()) {
			if (!first) {
				sb.append(entry.getValue().compareTo(BigInteger.ZERO) < 0 ? " - " : " + ");
			} else {
				if (entry.getValue().compareTo(BigInteger.ZERO) < 0) {
					sb.append("-");
				}
			}
			sb.append(entry.getValue().abs());
			sb.append("*");
			sb.append(entry.getKey());
			first = false;
		}
		if (!mConstant.equals(BigInteger.ZERO) || first) {
			if (!first) {
				sb.append(mConstant.compareTo(BigInteger.ZERO) < 0 ? " - " : " + ");
				sb.append(mConstant.abs());
			} else {
				sb.append(mConstant);
			}
		}
		return sb.toString();
	}

	private static Term constructSummand(final Script script, final Term t, final BigInteger coefficient) {
		if (coefficient.equals(BigInteger.ONE)) {
			return t;
		}
		return script.term("*", SmtUtils.constructIntValue(script, coefficient), t);
	}

	/**
	 * Return the affine-linear function as a SMTlib term
	 *
	 * @param script
	 *            the current script
	 * @return the generated term
	 * @throws SMTLIBException
	 */
	public Term asTerm(final Script script) throws SMTLIBException {
		final List<Term> summands = new ArrayList<>();
		for (final Map.Entry<IProgramVar, BigInteger> entry : mCoefficients.entrySet()) {
			final Term definition = ReplacementVarUtils.getDefinition(entry.getKey());
			summands.add(constructSummand(script, definition, entry.getValue()));
		}
		if (!mConstant.equals(BigInteger.ZERO)) {
			summands.add(SmtUtils.constructIntValue(script, mConstant));
		}
		return SmtUtils.sum(script, SmtSortUtils.getRealSort(script), summands.toArray(new Term[summands.size()]));
	}

	/**
	 * Evaluate this function for a variable assignment
	 *
	 * @param assignment
	 *            the assignment to the variables
	 * @return the value of the function
	 */
	public Rational evaluate(final Map<IProgramVar, Rational> assignment) {
		final Rational r = Rational.ZERO;
		for (final Map.Entry<IProgramVar, BigInteger> entry : mCoefficients.entrySet()) {
			Rational val = assignment.get(entry.getKey());
			if (val == null) {
				val = Rational.ZERO;
			}
			r.add(val.mul(entry.getValue()));
		}
		r.add(Rational.valueOf(mConstant, BigInteger.ONE));
		return r;
	}
}
