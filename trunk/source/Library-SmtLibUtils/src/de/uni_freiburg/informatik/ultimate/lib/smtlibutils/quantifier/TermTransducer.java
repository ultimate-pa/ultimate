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

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 * TODO 2020025 Matthias: Revise and add documentation.
 * Because of the SMT-COMP deadline, I committed this without documentation or code review.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public abstract class TermTransducer<E> {

	private Map<Term, E> mSubtermResult;



	public E transduce(final Term term) {
		mSubtermResult = new HashMap<>();
		final TermTransducer<E>.TermTransducerHelper tth = new TermTransducerHelper();
		tth.transform(term);
		final E result = mSubtermResult.get(term);
		mSubtermResult = null;
		return result;
	}

	protected abstract E transduceImmediately(Term term);

	protected abstract E transduce(ApplicationTerm appTerm, List<E> transducedArguments);



	private class TermTransducerHelper extends TermTransformer {

		@Override
		protected void convert(final Term term) {
			final E result = transduceImmediately(term);
			if (result == null) {
				super.convert(term);
			} else {
				setResult(term);
				mSubtermResult.put(term, result);
			}
		}

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
			final List<E> transducedArguments = Arrays.stream(appTerm.getParameters()).map(mSubtermResult::get)
					.collect(Collectors.toList());
			final E result = transduce(appTerm, transducedArguments);
			mSubtermResult.put(appTerm, result);
			super.convertApplicationTerm(appTerm, newArgs);
		}


		@Override
		public void preConvertLet(final LetTerm oldLet, final Term[] newValues) {
			super.preConvertLet(oldLet, newValues);
			throw new UnsupportedOperationException("not yet implemented");
		}

		@Override
		public void postConvertLet(final LetTerm oldLet, final Term[] newValues, final Term newBody) {
			super.postConvertLet(oldLet, newValues, newBody);
			throw new UnsupportedOperationException("not yet implemented");
		}

		@Override
		public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
			super.postConvertQuantifier(old, newBody);
			throw new UnsupportedOperationException("not yet implemented");
		}

		@Override
		public void postConvertAnnotation(final AnnotatedTerm old, final Annotation[] newAnnots, final Term newBody) {
			super.postConvertAnnotation(old, newAnnots, newBody);
			throw new UnsupportedOperationException("not yet implemented");
		}

		@Override
		public void preConvertMatchCase(final MatchTerm oldMatch, final int caseNr) {
			super.preConvertMatchCase(oldMatch, caseNr);
			throw new UnsupportedOperationException("not yet implemented");
		}

		@Override
		public void postConvertMatch(final MatchTerm oldMatch, final Term newDataTerm, final Term[] newCases) {
			super.postConvertMatch(oldMatch, newDataTerm, newCases);
			throw new UnsupportedOperationException("not yet implemented");
		}

	}

}
