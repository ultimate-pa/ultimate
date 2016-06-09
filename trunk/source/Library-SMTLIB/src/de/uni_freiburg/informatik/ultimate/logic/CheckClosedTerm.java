/*
 * Copyright (C) 2009-2014 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.logic;

import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

/**
 * Class to check if a term is closed.  It is closed if it does not contain
 * a free variable.  Use it as follows:
 * 
 * <pre>new CheckClosedTerm().isClosed()</pre>
 * 
 * You can check multiple terms with one instance and it will cache results
 * between checks.
 *
 * @author Jochen Hoenicke
 */
public class CheckClosedTerm extends NonRecursive {
	private final ScopedHashSet<Term> mCheckedTerms;
	private boolean mIsClosed;
	
	static class TermWalker implements NonRecursive.Walker {
		Term mTerm;
		
		public TermWalker(Term term) {
			mTerm = term;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			((CheckClosedTerm) engine).check(mTerm);
		}
	}
	
	static class EndScopeWalker implements NonRecursive.Walker {
		@Override
		public void walk(NonRecursive engine) {
			((CheckClosedTerm) engine).mCheckedTerms.endScope();
		}
	}

	/**
	 * The default constructor.
	 */
	public CheckClosedTerm() {
		mCheckedTerms = new ScopedHashSet<Term>();
	}

	/**
	 * Check if term t is closed. I.e., it contains no free term variable.
	 * @param t the term that is checked.
	 * @return true if the term is closed; false otherwise.
	 */
	public boolean isClosed(Term t) {
		mIsClosed = true;
		run(new TermWalker(t));
		return mIsClosed;
	}

	void check(Term t) {
		if (mCheckedTerms.contains(t) || !mIsClosed) {
			return;
		}
		mCheckedTerms.add(t);
		if (t instanceof ApplicationTerm) {
			for (final Term arg : ((ApplicationTerm)t).getParameters()) {
				enqueueWalker(new TermWalker(arg));
			}
		} else if (t instanceof AnnotatedTerm) {
			enqueueWalker(new TermWalker(((AnnotatedTerm)t).getSubterm()));
		} else if (t instanceof LetTerm) {
			final LetTerm let = (LetTerm) t;
			for (final Term value : let.getValues()) {
				enqueueWalker(new TermWalker(value));
			}
			mCheckedTerms.beginScope();
			enqueueWalker(new EndScopeWalker());
			for (final TermVariable var : let.getVariables()) {
				mCheckedTerms.add(var);
			}
			enqueueWalker(new TermWalker(let.getSubTerm()));
		} else if (t instanceof TermVariable) {
			/* all bound term variables were added to mCheckedTerms */
			mIsClosed = false;
		} else if (t instanceof QuantifiedFormula) {
			final QuantifiedFormula quant = (QuantifiedFormula) t;
			mCheckedTerms.beginScope();
			enqueueWalker(new EndScopeWalker());
			for (final TermVariable var : quant.getVariables()) {
				mCheckedTerms.add(var);
			}
			enqueueWalker(new TermWalker(quant.getSubformula()));
		} else if (!(t instanceof ConstantTerm)) {
			throw new AssertionError("Unknown term: " + t.getClass());
		}
	}
}
