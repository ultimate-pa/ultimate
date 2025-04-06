package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.AndTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.BooleanSelectTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.EqualsTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.FalseTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.GreaterEqualTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.GreaterTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.LessEqualTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.LessTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.NotTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.OrTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.TrueTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.VariableBooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.ITETerm;

public class TermNormalizer {
	/**
	 * @param term A {@link BooleanTerm} representing the transformula of an ICFG edge.<br>
	 *             Should be obtained by {@link #parseTerm(Term, HashMap)}
	 * @return An {@link OrTerm} whose subTerms are all {@link AndTerm}s (DNF), each representing a different path that
	 *         can be taken in this edge. All xor and implies terms are broken up into their logical components. There
	 *         are no other {@link AndTerm} or {@link OrTerm}s. {@link ITETerm}s have their condition replaced by an
	 *         internal Variable Term. The first ancestor that is a BooleanTerm is then wrapped by
	 *         {@code (and ancestor (var = condition))}. Similar things are done for array select indexes and array
	 *         store indexes and values. This means that for example an IntegerTerm can only have children that are also
	 *         IntegerTerms or Variables, they do not contain internal BitVector, Array or Boolean terms.
	 */
	public static OrTerm simplifyToDNF(BooleanTerm term) {
		BooleanTerm simpleTerm = term.simplify();
		while (!simpleTerm.equals(term)) {
			term = simpleTerm;
			simpleTerm = term.simplify();
		}

		ArrayList<BooleanTerm> andTerms = new ArrayList<>();
		if (simpleTerm instanceof OrTerm) {
			andTerms = ((OrTerm) simpleTerm).getSubTerms();
		} else {
			andTerms.add(simpleTerm);
		}

		for (int i = 0; i < andTerms.size(); i++) {
			BooleanTerm andTerm = andTerms.get(i);
			if (!(andTerm instanceof AndTerm)) {
				andTerm = new AndTerm(andTerm);
			}
			final ArrayList<BooleanTerm> restrictions = ((AndTerm) andTerm).getSubTerms();

			for (int j = 0; j < restrictions.size(); j++) {
				BooleanTerm restriction = restrictions.get(j);

				switch (restriction) {
				case final VariableBooleanTerm varBoolTerm:
					// and(..., bool_var, ...) = and(..., (bool_var = true), ...)
					restrictions.set(j, new EqualsTerm(restriction, new TrueTerm()).simplify());
					break;
				case final BooleanSelectTerm boolSelectTerm:
					// and(..., (select array_bool_var _), ...) = and(..., ((select array_bool_var _) = true), ...)
					restrictions.set(j, new EqualsTerm(restriction, new TrueTerm()).simplify());
					break;
				case final NotTerm notTerm:
					restriction = notTerm.getSubTerms().get(0);

					// and(..., (not bool_var), ...) = and(..., (bool_var = false), ...)
					if (restriction instanceof VariableBooleanTerm) {
						restrictions.set(j, new EqualsTerm(restriction, new FalseTerm()).simplify());
						continue;
					}

					// and(..., (not (select array_bool_var _)), ...) = and(..., ((select array_bool_var _) = false),
					// ...)
					if (restriction instanceof BooleanSelectTerm) {
						restrictions.set(j, new EqualsTerm(restriction, new FalseTerm()).simplify());
						continue;
					}
					break;
				// The comparison terms may have constructs like (1 + var_a) <= var_b that can be simplified to
				// var_a < var_b
				case final LessEqualTerm leqTerm:
					break;
				case final LessTerm lsTerm:
					break;
				case final GreaterEqualTerm geqTerm:
					break;
				case final GreaterTerm gtTerm:
					break;
				default:
					break;
				}
			}

			andTerms.set(i, new AndTerm(restrictions.toArray(new BooleanTerm[restrictions.size()])));
		}
		return new OrTerm(andTerms.toArray(new AndTerm[andTerms.size()]));
	}

	public static BooleanTerm eliminateITE(final BooleanTerm term) {
		return term; // TODO
	}
}
