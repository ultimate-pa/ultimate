package de.uni_freiburg.informatik.ultimate.lib.chc.eldarica;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

import ap.SimpleAPI;
import ap.parser.IAtom;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.ITerm;
import ap.terfor.preds.Predicate;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import lazabs.horn.bottomup.HornClauses;
import lazabs.horn.bottomup.HornClauses.Clause;
import lazabs.horn.bottomup.SimpleWrapper;
import scala.collection.JavaConverters;
import scala.collection.immutable.List;
import scala.runtime.AbstractFunction1;

public class EldaricaBridge {
	private final SimpleAPI mEldarica;

	private final Map<HcPredicateSymbol, Predicate> mPredicateMap = new HashMap<>();
	private final Map<TermVariable, ITerm> mVariableMap = new HashMap<>();

	public static void doStuff(final Script script, final java.util.Collection<HornClause> clauses) {
		SimpleAPI.<Object> withProver(new AbstractFunction1<>() {
			@Override
			public Object apply(final SimpleAPI p) {
				return new EldaricaBridge(script, p, clauses);
			}
		});
	}

	public EldaricaBridge(final Script script, final SimpleAPI eldarica,
			final java.util.Collection<HornClause> clauses) {
		mEldarica = eldarica;

		final var translated = clauses.stream().map(this::translateClause).collect(Collectors.toList());
		final var result = SimpleWrapper.solve(toList(translated), SimpleWrapper.solve$default$2(),
				SimpleWrapper.solve$default$3(), SimpleWrapper.solve$default$4(), SimpleWrapper.solve$default$5(),
				SimpleWrapper.solve$default$6());

		if (result.isLeft()) {
			System.out.println("SAT");
			final var solution = result.left().get();
		} else {
			System.out.println("UNSAT");
		}
	}

	private Clause translateClause(final HornClause clause) {
		final IAtom head;
		if (clause.isHeadFalse()) {
			head = new IAtom(HornClauses.FALSE(), null);
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
		return mEldarica.createRelation(pred.getName(), toList(sorts));
	}

	private ap.types.Sort translateSort(final Sort sort) {
		switch (sort.getName()) {
		case "Int":
			return new ap.types.Sort.Integer$();
		case "Bool":
			return new ap.types.Sort.MultipleValueBool$();
		default:
			throw new IllegalArgumentException(sort.getName());
		}
	}

	private IFormula translateFormula(final Term term) {
		return (IFormula) translateExpression(term);
	}

	private ITerm translateTerm(final Term term) {
		return (ITerm) translateExpression(term);
	}

	private IExpression translateExpression(final Term term) {
		if (term instanceof TermVariable) {
			return translateVariable((TermVariable) term);
		}
		if (term instanceof ApplicationTerm) {
			return translateApplication((ApplicationTerm) term);
		}
		throw new IllegalArgumentException(term.toString());
	}

	private IExpression translateVariable(final TermVariable variable) {
		return mVariableMap.computeIfAbsent(variable,
				v -> mEldarica.createConstant(v.getName(), translateSort(v.getSort())));
	}

	private IExpression translateApplication(final ApplicationTerm term) {
		switch (term.getFunction().getName()) {
		case "and":
			final var conjuncts =
					Arrays.stream(term.getParameters()).map(this::translateFormula).collect(Collectors.toList());
			return IExpression.and(toList(conjuncts));
		case "or":
			final var disjuncts =
					Arrays.stream(term.getParameters()).map(this::translateFormula).collect(Collectors.toList());
			return IExpression.or(toList(disjuncts));
		case "=>":
			final var first = translateFormula(term.getParameters()[0]);
			final var second = translateFormula(term.getParameters()[1]);
			return first.$eq$eq$greater(second);
		case "not":
			return translateFormula(term.getParameters()[0]).unary_$bang();
		case "=":
			return translateBinaryExpression(term, ITerm::$eq$eq$eq);
		case "distinct":
			return translateBinaryExpression(term, ITerm::$eq$div$eq);
		case "<":
			return translateBinaryExpression(term, ITerm::$less);
		case "<=":
			return translateBinaryExpression(term, ITerm::$less$eq);
		case ">":
			return translateBinaryExpression(term, ITerm::$greater);
		case ">=":
			return translateBinaryExpression(term, ITerm::$greater$eq);
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
}
