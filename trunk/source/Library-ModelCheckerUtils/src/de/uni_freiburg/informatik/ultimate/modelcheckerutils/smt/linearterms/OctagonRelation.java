/*
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;

/**
 * Affine relation of the form <i>(±x)-(±y) ≤ c</i> where <i>x</i> and <i>y</i> are (not necessarily different)
 * variables, <i>c</i> is a constant and <i>R</i> is one of the relations =, ≠, ≤, ≥, \<, \> from
 * {@link RelationSymbol}.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class OctagonRelation {

	private final boolean mNegateVar1;
	private final Term mVar1;
	private final boolean mNegateVar2;
	private final Term mVar2;
	private final RelationSymbol mRelationSymbol;
	private final Rational mConstant;

	public OctagonRelation(final boolean negateVar1, final Term var1, final boolean negateVar2, final Term var2,
			final RelationSymbol relationSymbol, final Rational constant) {
		mNegateVar1 = negateVar1;
		mVar1 = var1;
		mNegateVar2 = negateVar2;
		mVar2 = var2;
		mRelationSymbol = relationSymbol;
		mConstant = constant;
	}

	public static OctagonRelation from(final AffineRelation ar) {
		final Set<Term> variables = ar.getAffineTerm().getVariable2Coefficient().keySet();
		for (final Term v : variables) {
			if (!(v instanceof TermVariable || SmtUtils.isConstant(v))) {
				// If there is anything other than a variable or a constant, we cannot build an OctagonRelation
				return null;
			}
		}
		switch (variables.size()) {
		case 1:
			return from1Var(ar);
		case 2:
			return from2Vars(ar);
		default:
			return null;
		}

	}

	private static OctagonRelation from1Var(final AffineRelation arWith1Var) {
		checkNumberOfVariables(1, arWith1Var.getAffineTerm().getVariable2Coefficient().size());
		final Map.Entry<Term, Rational> var2coeff =
				arWith1Var.getAffineTerm().getVariable2Coefficient().entrySet().iterator().next();
		final Term var = var2coeff.getKey();
		final Rational absCoeff = var2coeff.getValue().abs();
		final boolean negVar = var2coeff.getValue().isNegative();
		// In AffineRelation the constant is left of the relation, but here it is right of the relation => negate
		final Rational constant = arWith1Var.getAffineTerm().getConstant().mul(Rational.TWO).div(absCoeff).negate();
		// 2x R c <==> (+x) - (-x) R c
		// -2x R c <==> (-x) - (+x) R c
		return new OctagonRelation(negVar, var, !negVar, var, arWith1Var.getRelationSymbol(), constant);
	}

	private static OctagonRelation from2Vars(final AffineRelation arWith2Vars) {
		final Map<Term, Rational> var2coeff = arWith2Vars.getAffineTerm().getVariable2Coefficient();
		checkNumberOfVariables(2, var2coeff.size());
		final Iterator<Map.Entry<Term, Rational>> iter = var2coeff.entrySet().iterator();
		final Map.Entry<Term, Rational> var2coeff1 = iter.next();
		final Map.Entry<Term, Rational> var2coeff2 = iter.next();
		final Rational absCommonCoeff = var2coeff1.getValue().abs();
		if (!absCommonCoeff.equals(var2coeff2.getValue().abs())) {
			// No common coefficient. (3x + 2y < c) cannot be converted to an octagon relation.
			return null;
		}
		// In AffineRelation the constant is left of the relation, but here it is right of the relation => negate
		final Rational constant = arWith2Vars.getAffineTerm().getConstant().div(absCommonCoeff).negate();
		return new OctagonRelation(var2coeff1.getValue().isNegative(), var2coeff1.getKey(),
				!var2coeff2.getValue().isNegative(), var2coeff2.getKey(), arWith2Vars.getRelationSymbol(), constant);
	}

	private static void checkNumberOfVariables(final int expected, final int actual) {
		if (expected != actual) {
			throw new IllegalArgumentException("Expected " + expected + " variable(s), found " + actual);
		}
	}

	public boolean isNegateVar1() {
		return mNegateVar1;
	}

	public Term getVar1() {
		return mVar1;
	}

	public boolean isNegateVar2() {
		return mNegateVar2;
	}

	public Term getVar2() {
		return mVar2;
	}

	public RelationSymbol getRelationSymbol() {
		return mRelationSymbol;
	}

	public Rational getConstant() {
		return mConstant;
	}

	@Override
	public String toString() {
		return String.format("(%s%s) - (%s%s) %s %s", sign(mNegateVar1), mVar1, sign(mNegateVar2), mVar2,
				mRelationSymbol, mConstant);
	}

	private static char sign(final boolean negate) {
		return negate ? '-' : '+';
	}

}
