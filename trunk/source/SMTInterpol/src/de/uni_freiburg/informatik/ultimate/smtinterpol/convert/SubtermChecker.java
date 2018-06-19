/*
 * Copyright (C) 2013 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class SubtermChecker extends NonRecursive {
	
	private static final class IsSubterm extends TermWalker {

		public IsSubterm(final Term term) {
			super(term);
		}

		@Override
		public void walk(final NonRecursive walker) {
			final SubtermChecker sc = (SubtermChecker) walker;
			if (getTerm() == sc.mSubTerm) {
				sc.mFound = true;
				// Clear the todo stack
				sc.done();
			} else {
				super.walk(walker);
			}
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			// Already checked in walk
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			walker.enqueueWalker(new IsSubterm(term.getSubterm()));
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			for (final Term p : term.getParameters()) {
				walker.enqueueWalker(new IsSubterm(p));
			}
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			throw new InternalError("LetTerms should not be present!");
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			walker.enqueueWalker(new IsSubterm(term.getSubformula()));
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			// Already checked in walk
		}
		
	}
	
	private final Term mSubTerm;
	private boolean mFound = false;
	
	public SubtermChecker(final Term subterm) {
		mSubTerm = subterm;
	}
	
	public boolean findSubterm(final Term where) {
		run(new IsSubterm(where));
		return mFound;
	}
	
	@Override
	public void reset() {
		super.reset();
		mFound = false;
	}
	
	private void done() {
		super.reset();
	}

}
