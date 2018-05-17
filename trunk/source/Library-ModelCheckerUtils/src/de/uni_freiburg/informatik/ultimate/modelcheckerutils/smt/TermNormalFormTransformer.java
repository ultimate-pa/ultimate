/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.simplifier.INormalFormable;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class TermNormalFormTransformer implements INormalFormable<Term> {

	private final Script mScript;
	private final Term mTrue;
	private final Term mFalse;

	public TermNormalFormTransformer(final Script script) {
		mScript = script;
		mTrue = mScript.term("true");
		mFalse = mScript.term("false");
	}

	@Override
	public Term changeForall(final Term oldForAll, final Term operand) {
		final QuantifiedFormula quant = (QuantifiedFormula) oldForAll;
		return mScript.quantifier(QuantifiedFormula.FORALL, quant.getVariables(), operand);
	}

	@Override
	public Term makeAnd(final Term next, final Term notor) {
		return mScript.term("and", next, notor);
	}

	@Override
	public Term makeFalse() {
		return mFalse;
	}

	@Override
	public Term makeTrue() {
		return mTrue;
	}

	@Override
	public Term changeExists(final Term oldExists, final Term operand) {
		final QuantifiedFormula quant = (QuantifiedFormula) oldExists;
		return mScript.quantifier(QuantifiedFormula.EXISTS, quant.getVariables(), operand);
	}

	@Override
	public Term makeOr(final Iterator<Term> operands) {
		return mScript.term("or", toArray(operands));
	}

	@Override
	public Term makeAnd(final Iterator<Term> operands) {
		return mScript.term("and", toArray(operands));
	}

	@Override
	public Term makeNot(final Term operand) {
		return mScript.term("not", operand);
	}

	@Override
	public Term getOperand(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appt = (ApplicationTerm) term;
			if (appt.getParameters().length == 1) {
				return appt.getParameters()[0];
			}
		}
		if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula quantf = (QuantifiedFormula) term;
			return quantf.getSubformula();
		}

		throw new IllegalArgumentException("Term " + term + " has no single operand");
	}

	@Override
	public Collection<? extends Term> normalizeNesting(final Term formula, final Term subformula) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Term rewritePredNotEquals(final Term atom) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Term negatePred(final Term atom) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterator<Term> getOperands(final Term formula) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isAtom(final Term formula) {
		return formula instanceof TermVariable || formula instanceof ConstantTerm;
	}

	@Override
	public boolean isLiteral(final Term formula) {
		if (isAtom(formula)) {
			return true;
		}
		if (formula instanceof ApplicationTerm) {
			final ApplicationTerm appl = (ApplicationTerm) formula;
			if ("not".equals(appl.getFunction().getName())) {
				final Term param = appl.getParameters()[0];
				return isAtom(param);
			}
		}
		return false;
	}

	@Override
	public boolean isNot(final Term formula) {
		return isFunctionApplication(formula, "not");
	}

	@Override
	public boolean isAnd(final Term formula) {
		return isFunctionApplication(formula, "and");
	}

	@Override
	public boolean isOr(final Term formula) {
		return isFunctionApplication(formula, "or");
	}

	@Override
	public boolean isExists(final Term formula) {
		return isQuantifier(formula, QuantifiedFormula.EXISTS);
	}

	@Override
	public boolean isForall(final Term formula) {
		return isQuantifier(formula, QuantifiedFormula.FORALL);
	}

	@Override
	public boolean isEqual(final Term one, final Term other) {
		return Objects.equals(one, other);
	}

	private static boolean isFunctionApplication(final Term formula, final String funName) {
		if (formula instanceof ApplicationTerm) {
			final ApplicationTerm appl = (ApplicationTerm) formula;
			return appl.getFunction().getName().equals(funName);
		}
		return false;
	}

	private static boolean isQuantifier(final Term formula, final int quantifier) {
		if (formula instanceof QuantifiedFormula) {
			final QuantifiedFormula quant = (QuantifiedFormula) formula;
			return quant.getQuantifier() == quantifier;
		}
		return false;
	}

	private static Term[] toArray(final Iterator<Term> operands) {
		final ArrayList<Term> list = new ArrayList<>();
		operands.forEachRemaining(list::add);
		final Term[] terms = list.toArray(new Term[list.size()]);
		return terms;
	}

	@Override
	public boolean isTrue(final Term formula) {
		return "true".equals(formula.toString());
	}

	@Override
	public boolean isFalse(final Term formula) {
		return "false".equals(formula.toString());
	}

}
