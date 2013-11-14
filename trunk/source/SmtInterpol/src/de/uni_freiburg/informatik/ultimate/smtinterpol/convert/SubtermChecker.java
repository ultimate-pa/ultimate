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

		public IsSubterm(Term term) {
			super(term);
		}

		@Override
		public void walk(NonRecursive walker) {
			SubtermChecker sc = (SubtermChecker) walker;
			if (getTerm() == sc.m_SubTerm) {
				sc.m_Found = true;
				// Clear the todo stack
				sc.done();
			} else if (getTerm() instanceof SMTAffineTerm) {
				SMTAffineTerm at = (SMTAffineTerm) getTerm();
				for (Term s : at.getSummands().keySet())
					walker.enqueueWalker(new IsSubterm(s));
			} else
				super.walk(walker);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new IsSubterm(term.getSubterm()));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			for (Term p : term.getParameters())
				walker.enqueueWalker(new IsSubterm(p));
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			throw new InternalError("LetTerms should not be present!");
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new IsSubterm(term.getSubformula()));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {}
		
	}
	
	private Term m_SubTerm;
	private boolean m_Found = false;
	
	public SubtermChecker(Term subterm) {
		m_SubTerm = subterm;
	}
	
	public boolean findSubterm(Term where) {
		run(new IsSubterm(where));
		return m_Found;
	}
	
	public void reset() {
		super.reset();
		m_Found = false;
	}
	
	private void done() {
		super.reset();
	}

}
