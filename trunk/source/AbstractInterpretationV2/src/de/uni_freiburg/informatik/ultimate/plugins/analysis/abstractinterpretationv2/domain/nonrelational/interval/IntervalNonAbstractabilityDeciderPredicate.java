package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.util.Arrays;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;

/**
 * Decides whether a term is not abstractable in the interval doamin.
 * {@link IntervalNonAbstractabilityDeciderPredicate#test(Term)} returns <code>true</code> iff the given term is not
 * abstractable, <code>false</code> otherwise.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalNonAbstractabilityDeciderPredicate implements Predicate<Term> {

	@Override
	public boolean test(final Term term) {
		if (term instanceof ApplicationTerm) {
			return decide((ApplicationTerm) term);
		} else if (term instanceof ConstantTerm) {
			return false;
		} else if (term instanceof TermVariable) {
			return false;
		}
		throw new UnsupportedOperationException(term.toString());
		// return true;
	}

	private boolean decide(final ApplicationTerm term) {
		final String function = term.getFunction().getName();

		switch (function) {
		case "and":
		case "or":
		case "not": // TODO: Does the occurrence of "not" imply abstractability? Do we need to rewrite this?
			// If any sub term is not abstractable, the whole term becomes not abstractable.
			return Arrays.stream(term.getParameters()).anyMatch(subTerm -> test(subTerm));
		case ">":
		case "<":
			// If all are subterms are of sort int, the term a < c can be expressed as a <= c + 1 and is therefore
			// abstractable.
			if (!Arrays.stream(term.getParameters())
					.allMatch(subTerm -> SmtSortUtils.isIntSort(subTerm.getSort().getRealSort()))) {
				return true;
			}
		case ">=":
		case "<=":
		case "=":
			if (term.getParameters().length != 2) {
				return true;
			}

			// If var <OP> c or c <OP> var, then this is abstractable in intervals.
			if ((term.getParameters()[0] instanceof TermVariable && term.getParameters()[1] instanceof ConstantTerm)
					|| (term.getParameters()[0] instanceof ConstantTerm
							&& term.getParameters()[1] instanceof TermVariable)) {
				return false;
			}

			// TODO: what about bool1 = bool2?
			return true;
		default:
			throw new UnsupportedOperationException(term.toString());
		}
	}
}
