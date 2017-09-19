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
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class DAGSize extends NonRecursive {
	
	private class TreeSizeCache implements NonRecursive.Walker {
		long mSizeBefore = 0;
		Term mTerm;

		public TreeSizeCache(Term term) {
			mSizeBefore = mSize;
			mTerm = term;
		}

		@Override
		public void walk(NonRecursive walker) {
			mCache.put(mTerm, mSize - mSizeBefore);
		}
	}

	private class TermOnceWalker extends NonRecursive.TermWalker {

		public TermOnceWalker(Term term) {
			super(term);
		}

		@Override
		public void walk(NonRecursive walker) {
			if (mCache.containsKey(mTerm)) {
				if (mComputeTreeSize)
					mSize += mCache.get(mTerm);
				return;
			}
			if (mComputeTreeSize) {
				enqueueWalker(new TreeSizeCache(mTerm));
			} else {
				mCache.put(mTerm, Long.valueOf(0));
			}
			++mSize;
			super.walk(walker);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// No subterms to enqueue
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			// TODO Do we want to count annotations???
			walker.enqueueWalker(new TermOnceWalker(term.getSubterm()));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			for (final Term t : term.getParameters()) {
				walker.enqueueWalker(new TermOnceWalker(t));
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			throw new InternalError("Input should be unletted");
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new TermOnceWalker(term.getSubformula()));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			// No subterms to enqueue
		}
	}

	private Map<Term, Long> mCache;
	private boolean mComputeTreeSize;
	private long mSize;
	
	public DAGSize() {
		mCache = new HashMap<Term, Long>();
		mSize = 0;
	}
	
	@Override
	public void reset() {
		super.reset();
		mCache.clear();
		mSize = 0;
	}
	
	public int size(Term term) {
		mComputeTreeSize = false;
		run(new TermOnceWalker(new FormulaUnLet().unlet(term)));
		return (int) mSize;
	}
	
	public long treesize(Term term) {
		mComputeTreeSize = true;
		run(new TermOnceWalker(new FormulaUnLet().unlet(term)));
		return mSize;
	}
}
