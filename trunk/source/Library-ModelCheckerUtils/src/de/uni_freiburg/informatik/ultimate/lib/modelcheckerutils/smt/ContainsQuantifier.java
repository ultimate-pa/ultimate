/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Check if term contains some quantified subformula.
 * @author Matthias Heizmann
 * @deprecated Use {@link QuantifierUtils#isQuantifierFree(Term)} instead.
 *
 */
@Deprecated
public class ContainsQuantifier extends NonRecursive {

	private boolean mQuantifierFound;
	private int mFirstQuantifierFound = -1;
	private Set<Term> mTermsInWhichWeAlreadyDescended;

	class QuantifierFinder extends TermWalker {
		QuantifierFinder(final Term term) { super(term); }


		@Override
		public void walk(final NonRecursive walker) {
			if (mQuantifierFound) {
				// do nothing
			} else {
				if (mTermsInWhichWeAlreadyDescended.contains(getTerm())) {
					// do nothing
				} else {
					super.walk(walker);
				}
			}
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			// cannot descend
		}
		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			walker.enqueueWalker(new QuantifierFinder(term.getSubterm()));
		}
		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			mTermsInWhichWeAlreadyDescended.add(term);
			for (final Term t : term.getParameters()) {
				walker.enqueueWalker(new QuantifierFinder(t));
			}
		}
		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			walker.enqueueWalker(new QuantifierFinder(term.getSubTerm()));
		}
		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			mQuantifierFound = true;
			mFirstQuantifierFound = term.getQuantifier();
			reset();
		}
		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			// cannot descend
		}
	}

	/**
	 * Returns true iff this term contains the subterm of this ContainsSubterm
	 * object.
	 */
	public boolean containsQuantifier(final Term term) {
		mFirstQuantifierFound = -1;
		mQuantifierFound = false;
		assert mTermsInWhichWeAlreadyDescended == null;
		mTermsInWhichWeAlreadyDescended = new HashSet<>();
		run(new QuantifierFinder(term));
		mTermsInWhichWeAlreadyDescended = null;
		return mQuantifierFound;
	}

	public int getFirstQuantifierFound() {
		if (mFirstQuantifierFound == -1) {
			throw new IllegalStateException("no quantifier found");
		}
		return mFirstQuantifierFound;
	}
}
