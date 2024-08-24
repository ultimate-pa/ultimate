/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * TODO 2020025 Matthias: Revise and add documentation.
 * Because of the SMT-COMP deadline, I committed this without documentation or code review.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public abstract class CondisTermTransducer<E> extends TermTransducer<E> {

	protected abstract E transduceAtom(Term term);

	protected abstract E transduceConjunction(ApplicationTerm originalTerm, List<E> transducedArguments);

	protected abstract E transduceDisjunction(ApplicationTerm originalTerm, List<E> transducedArguments);

	private static boolean isConjunction(final Term term) {
		return (term instanceof ApplicationTerm) && ((ApplicationTerm) term).getFunction().getName().equals("and");
	}

	private static boolean isDisjunction(final Term term) {
		return (term instanceof ApplicationTerm) && ((ApplicationTerm) term).getFunction().getName().equals("or");
	}

	@Override
	protected E transduceImmediately(final Term term) {
		E result;
		if (isConjunction(term)) {
			// let TermTransducer descend to subterms
			result = null;
		} else if (isDisjunction(term)) {
			result = null;
			// let TermTransducer descend to subterms
		} else {
			result = transduceAtom(term);
		}
		return result;
	}

	@Override
	protected E transduce(final ApplicationTerm originalTerm, final List<E> transducedArguments) {
		E result;
		if (isConjunction(originalTerm)) {
			result = transduceConjunction(originalTerm, transducedArguments);
		} else if (isDisjunction(originalTerm)) {
			result = transduceDisjunction(originalTerm, transducedArguments);
		} else {
			throw new AssertionError("neither conjunction nor disjunction");
		}
		return result;
	}

}
