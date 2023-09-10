/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE CHC Library.
 *
 * The ULTIMATE CHC Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CHC Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CHC Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CHC Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CHC Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.chc.eldarica;

import java.math.BigInteger;

import ap.parser.IBinFormula;
import ap.parser.IBinJunctor;
import ap.parser.IEquation;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IIntFormula;
import ap.parser.IIntLit;
import ap.parser.IIntRelation;
import ap.parser.IPlus;
import ap.parser.ISortedVariable;
import ap.parser.ITerm;
import ap.parser.ITimes;
import ap.terfor.preds.Predicate;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;

/**
 * Backtranslation from eldarica terms and formulas to Ultimate terms.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
class Backtranslator {
	private final Script mScript;
	private final BidirectionalMap<HcPredicateSymbol, Predicate> mPredicateMap;

	Backtranslator(final Script script, final BidirectionalMap<HcPredicateSymbol, Predicate> predicateMap) {
		mScript = script;
		mPredicateMap = predicateMap;
	}

	public HcPredicateSymbol translatePredicate(final Predicate predicate) {
		return mPredicateMap.inverse().get(predicate);
	}

	public Term translateFormula(final IFormula formula, final IBoundVariableContext ctx) {
		if (formula instanceof IBinFormula) {
			return translateBinFormula((IBinFormula) formula, ctx);
		}
		if (formula instanceof IIntFormula) {
			return translateIntFormula((IIntFormula) formula, ctx);
		}
		if (formula instanceof IEquation) {
			return translateEquation((IEquation) formula, ctx);
		}
		throw new UnsupportedOperationException(formula.toString());
	}

	private Term translateEquation(final IEquation equation, final IBoundVariableContext ctx) {
		// We don't know the intended sort of the terms here. But it does not matter, equality works for all sorts.
		final var left = translateTermInternal(equation.left(), ctx);
		final var right = translateTermInternal(equation.right(), ctx);
		return SmtUtils.binaryEquality(mScript, left, right);
	}

	private Term translateIntFormula(final IIntFormula formula, final IBoundVariableContext ctx) {
		final var operand = translateTerm(formula.t(), getIntSort(), ctx);
		final var rel = formula.rel();
		if (IIntRelation.EqZero().equals(rel)) {
			return SmtUtils.binaryEquality(mScript, operand, numeral(BigInteger.ZERO));
		}
		if (IIntRelation.GeqZero().equals(rel)) {
			return SmtUtils.geq(mScript, operand, numeral(BigInteger.ZERO));
		}
		throw new UnsupportedOperationException("Unknown integer relation: " + rel);
	}

	private Term translateBinFormula(final IBinFormula formula, final IBoundVariableContext ctx) {
		final var left = translateFormula(formula.f1(), ctx);
		final var right = translateFormula(formula.f2(), ctx);

		final var op = formula.j();
		if (IBinJunctor.Or().equals(op)) {
			return SmtUtils.or(mScript, left, right);
		}
		if (IBinJunctor.And().equals(op)) {
			return SmtUtils.and(mScript, left, right);
		}
		if (IBinJunctor.Eqv().equals(op)) {
			return SmtUtils.binaryBooleanEquality(mScript, left, right);
		}
		throw new UnsupportedOperationException("Unknown binary operator: " + op);
	}

	public Term translateTerm(final ITerm term, final Sort sort, final IBoundVariableContext ctx) {
		// sort conversion for booleans: bool expected, but term given
		if (SmtSortUtils.isBoolSort(sort)) {
			final var formula = new ap.types.Sort.MultipleValueBool$().isTrue(term);
			return translateFormula(formula, ctx);
		}

		final var translated = translateTermInternal(term, ctx);

		// sort conversion for booleans: term expected, but translated sort is bool
		if (SmtSortUtils.isBoolSort(translated.getSort())) {
			// zero is true, non-zero is false
			// http://www.philipp.ruemmer.org/princess/doc/#ap.types.Sort$$MultipleValueBool$
			final var trueTerm = numeral(BigInteger.ZERO);
			final var falseTerm = numeral(BigInteger.ONE);
			return SmtUtils.ite(mScript, translated, trueTerm, falseTerm);
		}

		assert translated.getSort().equals(sort) : "Translated term has sort " + translated.getSort() + " instead of "
				+ sort;
		return translated;
	}

	private Term translateTermInternal(final ITerm term, final IBoundVariableContext ctx) {
		if (term instanceof IPlus) {
			final var plus = (IPlus) term;
			final var left = translateTerm(plus.t1(), getIntSort(), ctx);
			final var right = translateTerm(plus.t2(), getIntSort(), ctx);
			return SmtUtils.sum(mScript, getIntSort(), left, right);
		}
		if (term instanceof ITimes) {
			final var times = (ITimes) term;
			final var left = Rational.valueOf(times.coeff().bigIntValue(), BigInteger.ONE);
			final var right = translateTerm(times.subterm(), getIntSort(), ctx);
			return SmtUtils.mul(mScript, left, right);
		}
		if (term instanceof ISortedVariable) {
			final var variable = (ISortedVariable) term;
			return ctx.getBoundVariable(variable.index());
		}
		if (term instanceof IFunApp) {
			final var app = (IFunApp) term;
			final var storeTerm = translateStore(app, ctx);
			if (storeTerm != null) {
				return storeTerm;
			}
			final var constTerm = translateConstArray(app, ctx);
			if (constTerm != null) {
				return constTerm;
			}
			final var boolLit = translateBoolLit(app);
			if (boolLit != null) {
				return boolLit;
			}
		}
		if (term instanceof IIntLit) {
			final var value = ((IIntLit) term).value();
			return numeral(value.bigIntValue());
		}
		throw new IllegalArgumentException("Unknown term: " + term.toString());
	}

	private Term translateStore(final IFunApp store, final IBoundVariableContext ctx) {
		if (!SMTLIBConstants.STORE.equals(store.fun().name()) || store.fun().arity() != 3) {
			return null;
		}

		final var array = translateTermInternal(store.args().apply(0), ctx);
		final var index = translateTermInternal(store.args().apply(1), ctx);
		final var value = translateTermInternal(store.args().apply(2), ctx);

		return SmtUtils.store(mScript, array, index, value);
	}

	private Term translateConstArray(final IFunApp constArray, final IBoundVariableContext ctx) {
		if (!SMTLIBConstants.CONST.equals(constArray.fun().name()) || constArray.fun().arity() != 1) {
			return null;
		}

		final var value = translateTermInternal(constArray.args().apply(0), ctx);
		return mScript.term(SMTLIBConstants.CONST, null,
				SmtSortUtils.getArraySort(mScript, getIntSort(), value.getSort()), value);
	}

	private Term translateBoolLit(final IFunApp boolLit) {
		final var name = boolLit.fun().name();
		switch (name) {
		case SMTLIBConstants.TRUE:
		case SMTLIBConstants.FALSE:
			assert boolLit.args().isEmpty() : "unexpected parameters for function " + name;
			return mScript.term(name);
		default:
			return null;
		}
	}

	private Term numeral(final BigInteger value) {
		return SmtUtils.constructIntegerValue(mScript, getIntSort(), value);
	}

	private Sort getIntSort() {
		return SmtSortUtils.getIntSort(mScript);
	}

	public interface IBoundVariableContext {
		Term getBoundVariable(int index);
	}
}
