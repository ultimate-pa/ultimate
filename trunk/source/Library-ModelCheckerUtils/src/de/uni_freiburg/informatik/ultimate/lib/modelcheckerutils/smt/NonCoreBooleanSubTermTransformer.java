/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 * Transform non-CoreBoolean subterms of a term. Here, we call a term non-CoreBoolean if it is not an ApplicationTerm
 * whose connective is defined by the core theory and whose parameters dot not all have sort Bool.
 *
 * @author Matthias Heizmann
 *
 */
public abstract class NonCoreBooleanSubTermTransformer {

	private NonCoreBooleanSubtermTransformerHelper mTransformerHelper;

	public Term transform(final Term term) {
		if (!SmtSortUtils.isBoolSort(term.getSort())) {
			throw new IllegalArgumentException("Input term of sort Bool");
		}
		mTransformerHelper = new NonCoreBooleanSubtermTransformerHelper();
		final Term result = mTransformerHelper.transform(term);
		return result;
	}

	private static boolean hasBooleanParams(final Term[] parameters) {
		for (final Term term : parameters) {
			if (!SmtSortUtils.isBoolSort(term.getSort())) {
				return false;
			}
		}
		return true;
	}

	private static boolean isCoreBooleanConnective(final String fun) {
		if (fun.equals("=")) {
			return true;
		} else if (fun.equals("not")) {
			return true;
		} else if (fun.equals("and")) {
			return true;
		} else if (fun.equals("or")) {
			return true;
		} else if (fun.equals("=>")) {
			return true;
		} else if (fun.equals("xor")) {
			return true;
		} else if (fun.equals("distinct")) {
			return true;
		}
		return fun.equals("ite");
	}

	public static boolean isCoreBoolean(final ApplicationTerm appTerm) {
		final String funName = appTerm.getFunction().getName();
		return isCoreBooleanConnective(funName) && hasBooleanParams(appTerm.getParameters());

	}

	private class NonCoreBooleanSubtermTransformerHelper extends TermTransformer {

		@Override
		protected void convert(final Term term) {
			assert SmtSortUtils.isBoolSort(term.getSort()) : "not Bool";
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (isCoreBoolean(appTerm)) {
					super.convert(term);
				} else {
					final Term transformed = transformNonCoreBooleanSubterm(term);
					setResult(transformed);
					return;
				}
			} else if (term instanceof LetTerm) {
				throw new UnsupportedOperationException(NonCoreBooleanSubTermTransformer.class.getSimpleName()
						+ " does not support " + LetTerm.class.getSimpleName());
			} else if (term instanceof AnnotatedTerm) {
				throw new UnsupportedOperationException(NonCoreBooleanSubTermTransformer.class.getSimpleName()
						+ " does not support " + AnnotatedTerm.class.getSimpleName());
			}
			super.convert(term);
		}


	}

	protected abstract Term transformNonCoreBooleanSubterm(Term term);

}
