/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.util.Arrays;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

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
		case "select":
		case "store":
			// TODO: Handle array access.
			return true;
		default:
			throw new UnsupportedOperationException(term.toString());
		}
	}
}
