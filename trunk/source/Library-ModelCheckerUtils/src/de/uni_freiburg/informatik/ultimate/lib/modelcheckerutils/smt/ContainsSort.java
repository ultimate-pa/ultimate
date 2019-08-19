/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Check if term subterm whose sort is contained in a given set of sorts.
 *
 * @author Matthias Heizmann
 *
 */
public class ContainsSort extends NonRecursive {

	private Set<Term> mTermsInWhichWeAlreadyDescended;

	private final Set<String> mGivenSorts;
	private boolean mFoundInCurrentSeach;

	public ContainsSort(final Set<String> givenSorts) {
		super();
		mGivenSorts = givenSorts;
	}

	/**
	 * Returns true iff there is a subterm whose {@link Sort} is one of the given sorts.
	 */
	public boolean containsSubtermOfGivenSort(final Term term) {
		mFoundInCurrentSeach = false;
		mTermsInWhichWeAlreadyDescended = new HashSet<>();
		run(new MyWalker(term));
		mTermsInWhichWeAlreadyDescended = null;
		return mFoundInCurrentSeach;
	}

	private final class MyWalker extends TermWalker {
		MyWalker(final Term term) {
			super(term);
		}

		@Override
		public void walk(final NonRecursive walker) {
			if (mFoundInCurrentSeach) {
				// do nothing
			} else {
				if (mTermsInWhichWeAlreadyDescended.contains(getTerm())) {
					// do nothing
				} else {
					final Sort currentSort = getTerm().getSort();
					if (mGivenSorts.contains(currentSort.getName())) {
						mFoundInCurrentSeach = true;
						reset();
					} else {
						super.walk(walker);
					}
				}
			}
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			// cannot descend
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			mTermsInWhichWeAlreadyDescended.add(term);
			walker.enqueueWalker(new MyWalker(term.getSubterm()));
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			mTermsInWhichWeAlreadyDescended.add(term);
			for (final Term t : term.getParameters()) {
				walker.enqueueWalker(new MyWalker(t));
			}
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			walker.enqueueWalker(new MyWalker(term.getSubformula()));
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			// cannot descend
		}
	}
}
