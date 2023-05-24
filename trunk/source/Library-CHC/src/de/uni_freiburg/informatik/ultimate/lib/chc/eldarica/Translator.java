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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

import ap.SimpleAPI;
import ap.basetypes.IdealInt;
import ap.parser.IAtom;
import ap.parser.IBoolLit;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IIntLit;
import ap.parser.ITerm;
import ap.terfor.preds.Predicate;
import ap.theories.ExtArray;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import lazabs.horn.bottomup.HornClauses;
import lazabs.horn.bottomup.HornClauses.Clause;
import scala.collection.JavaConverters;
import scala.collection.immutable.List;

/**
 * Translates {@link HornClause}s to eldarica's {@link Clause}s.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
class Translator {
	private static final Map<String, BiFunction<ITerm, ITerm, IExpression>> BINARY_EXPRESSION_TRANSLATION = Map.of(
			// equality
			SMTLIBConstants.EQUALS, ITerm::$eq$eq$eq,
			// disequality
			SMTLIBConstants.DISTINCT, ITerm::$eq$div$eq,
			// less-than
			SMTLIBConstants.LT, ITerm::$less,
			// less-or-equal
			SMTLIBConstants.LEQ, ITerm::$less$eq,
			// greater-than
			SMTLIBConstants.GT, ITerm::$greater,
			// greater-or-equal
			SMTLIBConstants.GEQ, ITerm::$greater$eq,
			// addition
			SMTLIBConstants.PLUS, ITerm::$plus,
			// subtraction
			SMTLIBConstants.MINUS, ITerm::$minus);

	private final SimpleAPI mPrincess;
	private final BidirectionalMap<HcPredicateSymbol, Predicate> mPredicateMap = new BidirectionalMap<>();
	private final BidirectionalMap<TermVariable, ITerm> mVariableMap = new BidirectionalMap<>();
	private final NestedMap2<List<ap.types.Sort>, ap.types.Sort, ExtArray> mArrayTheories = new NestedMap2<>();

	public Translator(final SimpleAPI princess) {
		mPrincess = princess;
	}

	public Backtranslator createBacktranslator(final Script script) {
		return new Backtranslator(script, mPredicateMap);
	}

	public Clause translateClause(final HornClause clause) {
		final IAtom head;
		if (clause.isHeadFalse()) {
			head = new IAtom(HornClauses.FALSE(), toList(java.util.List.of()));
		} else {
			final var headPred = getPredicateSymbol(clause.getHeadPredicate());
			final var headArgs = clause.getTermVariablesForHeadPred().stream().map(HcHeadVar::getTermVariable)
					.map(this::translateTerm).collect(Collectors.toList());
			head = new IAtom(headPred, toList(headArgs));
		}

		final ArrayList<IAtom> body = new ArrayList<>(clause.getRank());
		for (int i = 0; i < clause.getRank(); ++i) {
			final var pred = getPredicateSymbol(clause.getBodyPredicates().get(i));
			final var args =
					clause.getBodyPredToArgs().get(i).stream().map(this::translateTerm).collect(Collectors.toList());
			body.add(new IAtom(pred, toList(args)));
		}

		final var constraint = translateFormula(clause.getConstraintFormula());
		return new Clause(head, toList(body), constraint);
	}

	private static <X> List<X> toList(final java.util.List<X> list) {
		return JavaConverters.asScalaIteratorConverter(list.iterator()).asScala().toList();
	}

	private Predicate getPredicateSymbol(final HcPredicateSymbol pred) {
		return mPredicateMap.computeIfAbsent(pred, this::createPredicate);
	}

	private Predicate createPredicate(final HcPredicateSymbol pred) {
		final var sorts = pred.getParameterSorts().stream().map(this::translateSort).collect(Collectors.toList());
		return mPrincess.createRelation(pred.getName(), toList(sorts));
	}

	private ap.types.Sort translateSort(final Sort sort) {
		if (SmtSortUtils.isIntSort(sort)) {
			return new ap.types.Sort.Integer$();
		}
		if (SmtSortUtils.isBoolSort(sort)) {
			return new ap.types.Sort.MultipleValueBool$();
		}
		if (SmtSortUtils.isArraySort(sort)) {
			return getArrayTheory(sort).sort();
		}
		throw new IllegalArgumentException(sort.getName());
	}

	private ExtArray getArrayTheory(final Sort arraySort) {
		final var params = arraySort.getArguments();
		assert params.length >= 2 : "arrays should have at least one index sort, and one domain sort";

		final var indices = toList(
				Arrays.stream(params).limit(params.length - 1).map(this::translateSort).collect(Collectors.toList()));
		final var range = translateSort(params[params.length - 1]);

		var theory = mArrayTheories.get(indices, range);
		if (theory == null) {
			theory = new ExtArray(indices, range);
			mArrayTheories.put(indices, range, theory);
		}
		return theory;
	}

	public IFormula translateFormula(final Term term) {
		final var expr = translateExpression(term);
		if (expr instanceof ITerm) {
			return new ap.types.Sort.MultipleValueBool$().isTrue((ITerm) expr);
		}
		return (IFormula) translateExpression(term);
	}

	public ITerm translateTerm(final Term term) {
		final var expr = translateExpression(term);
		if (expr instanceof IFormula) {
			final var bool = new ap.types.Sort.MultipleValueBool$();
			return IExpression.ite((IFormula) expr, bool.True(), bool.False());
		}
		return (ITerm) translateExpression(term);
	}

	private IExpression translateExpression(final Term term) {
		if (term instanceof TermVariable) {
			return translateVariable((TermVariable) term);
		}
		if (term instanceof ApplicationTerm) {
			return translateApplication((ApplicationTerm) term);
		}
		if (term instanceof ConstantTerm) {
			return translateConstant((ConstantTerm) term);
		}
		throw new IllegalArgumentException(term.toString());
	}

	private IExpression translateVariable(final TermVariable variable) {
		return mVariableMap.computeIfAbsent(variable, this::createVariable);
	}

	private ITerm createVariable(final TermVariable variable) {
		final var sort = variable.getSort();
		return mPrincess.createConstant(variable.getName(), translateSort(sort));
	}

	private IExpression translateApplication(final ApplicationTerm term) {
		final var function = term.getFunction().getName();

		final var binaryTranslation = BINARY_EXPRESSION_TRANSLATION.get(function);
		if (binaryTranslation != null) {
			return translateBinaryExpression(term, binaryTranslation);
		}

		switch (term.getFunction().getName()) {
		case SMTLIBConstants.TRUE:
		case SMTLIBConstants.FALSE:
			final var name = term.getFunction().getName();
			assert term.getParameters().length == 0 : "Unexpected parameters for function " + name;
			return new IBoolLit(Boolean.parseBoolean(name));
		case SMTLIBConstants.AND:
			final var conjuncts =
					Arrays.stream(term.getParameters()).map(this::translateFormula).collect(Collectors.toList());
			return IExpression.and(toList(conjuncts));
		case SMTLIBConstants.OR:
			final var disjuncts =
					Arrays.stream(term.getParameters()).map(this::translateFormula).collect(Collectors.toList());
			return IExpression.or(toList(disjuncts));
		case SMTLIBConstants.IMPLIES:
			final var first = translateFormula(term.getParameters()[0]);
			final var second = translateFormula(term.getParameters()[1]);
			return first.$eq$eq$greater(second);
		case SMTLIBConstants.NOT:
			return translateFormula(term.getParameters()[0]).unary_$bang();
		case SMTLIBConstants.ITE:
			final var cond = translateFormula(term.getParameters()[0]);
			final var thenCase = translateTerm(term.getParameters()[1]);
			final var elseCase = translateTerm(term.getParameters()[2]);
			return IExpression.ite(cond, thenCase, elseCase);
		case SMTLIBConstants.STORE:
			final var array = translateTerm(term.getParameters()[0]);
			final var index = translateTerm(term.getParameters()[1]);
			final var value = translateTerm(term.getParameters()[2]);
			return new IFunApp(getArrayTheory(term.getParameters()[0].getSort()).store(),
					toList(java.util.List.of(array, index, value)));
		case SMTLIBConstants.SELECT:
			final var selectArray = translateTerm(term.getParameters()[0]);
			final var selectIndex = translateTerm(term.getParameters()[1]);
			return new IFunApp(getArrayTheory(term.getParameters()[0].getSort()).select(),
					toList(java.util.List.of(selectArray, selectIndex)));
		default:
			throw new IllegalArgumentException(term.toString());
		}
	}

	private IExpression translateBinaryExpression(final ApplicationTerm term,
			final BiFunction<ITerm, ITerm, IExpression> combinator) {
		assert term.getParameters().length == 2;
		final var first = translateTerm(term.getParameters()[0]);
		final var second = translateTerm(term.getParameters()[1]);
		return combinator.apply(first, second);
	}

	private static ITerm translateConstant(final ConstantTerm constant) {
		final var value = constant.getValue();
		BigInteger bigint;
		if (value instanceof Rational) {
			assert ((Rational) value).denominator().equals(BigInteger.ONE);
			bigint = ((Rational) value).numerator();
		} else if (value instanceof BigInteger) {
			bigint = (BigInteger) value;
		} else {
			throw new IllegalArgumentException(constant.toString());
		}
		return new IIntLit(IdealInt.apply(bigint));
	}
}
