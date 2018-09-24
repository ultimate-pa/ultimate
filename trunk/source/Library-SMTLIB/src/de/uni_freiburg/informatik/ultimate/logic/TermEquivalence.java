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
package de.uni_freiburg.informatik.ultimate.logic;

import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * This class checks if two terms are syntactically equivalent modulo renaming of variables. E. g.,
 * <code>(let ((x 0)) x)</code> is equivalent to <code>(let ((y 0)) y)</code>, but not to <code>0</code> or
 * <code>(let ((y 0)) 0)</code>.
 * 
 * @author Juergen Christ, Jochen Hoenicke
 */
public class TermEquivalence extends NonRecursive {
	
	private final ScopedHashMap<TermVariable, TermVariable> mRenaming =
			new ScopedHashMap<TermVariable, TermVariable>();
	
	private void beginScope() {
		mRenaming.beginScope();
	}
	
	private void endScope() {
		mRenaming.endScope();
	}
	
	private void addRenaming(TermVariable lvar, TermVariable rvar) {
		mRenaming.put(lvar, rvar);
	}
	
	private boolean checkRenaming(TermVariable lvar, TermVariable rvar) {
		return mRenaming.get(lvar) == rvar;
	}
	
	@SuppressWarnings("serial")
	private static final class NotEq extends RuntimeException {
		// Empty control flow exception
	}
	
	private final static class EndScope implements Walker {
		public final static EndScope INSTANCE = new EndScope();
		@Override
		public void walk(NonRecursive engine) {
			final TermEquivalence te = (TermEquivalence) engine;
			te.endScope();
		}
	}
	
	private final static class AddRenaming implements Walker {
		private final TermVariable mLvar, mRvar;
		public AddRenaming(TermVariable lvar, TermVariable rvar) {
			mLvar = lvar;
			mRvar = rvar;
		}
		@Override
		public void walk(NonRecursive engine) {
			final TermEquivalence te = (TermEquivalence) engine;
			te.addRenaming(mLvar, mRvar);
		}
	}

	private final static class TermEq implements Walker {

		private final Term mLhs, mRhs;
		
		public TermEq(Term lhs, Term rhs) {
			mLhs = lhs;
			mRhs = rhs;
		}
		
		private final void notEqual() {
			throw new NotEq();
		}
		
		@Override
		public void walk(NonRecursive engine) {
			final TermEquivalence te = (TermEquivalence) engine;
			if (mLhs != mRhs) {
				if (mLhs.getClass() != mRhs.getClass()) {
					// Cannot be equal
					notEqual();
				}
				if (mLhs instanceof ApplicationTerm) {
					final ApplicationTerm l = (ApplicationTerm) mLhs;
					final ApplicationTerm r = (ApplicationTerm) mRhs;
					if (l.getFunction() != r.getFunction()) {
						notEqual();
					}
					final Term[] lparams = l.getParameters();
					final Term[] rparams = r.getParameters();
					if (lparams.length != rparams.length) {
						notEqual();
					}
					for (int i = 0; i < lparams.length; ++i) {
						te.enqueueWalker(new TermEq(lparams[i], rparams[i]));
					}
				} else if (mLhs instanceof AnnotatedTerm) {
					final AnnotatedTerm l = (AnnotatedTerm) mLhs;
					final AnnotatedTerm r = (AnnotatedTerm) mRhs;
					final Annotation[] lannot = l.getAnnotations();
					final Annotation[] rannot = r.getAnnotations();
					if (rannot.length != lannot.length) {
						notEqual();
					}
					for (int i = 0; i < lannot.length; ++i) {
						if (!lannot[i].getKey().equals(rannot[i].getKey())) {
							notEqual();
						}
						if (lannot[i].getValue() instanceof Term
								&& rannot[i].getValue() instanceof Term) {
							te.enqueueWalker(new TermEq(
									(Term) lannot[i].getValue(),
									(Term) rannot[i].getValue()));
						} else if (lannot[i].getValue() instanceof Object[]
								&& rannot[i].getValue() instanceof Object[]) {
							te.enqueueWalker(
									new ArrayEq((Object[]) lannot[i].getValue(), (Object[]) rannot[i].getValue()));
						} else if (!lannot[i].getValue().equals(rannot[i].getValue())) {
							notEqual();
						}
					}
				} else if (mLhs instanceof LetTerm) {
					final LetTerm llet = (LetTerm) mLhs;
					final LetTerm rlet = (LetTerm) mRhs;
					final TermVariable[] lvars = llet.getVariables();
					final TermVariable[] rvars = rlet.getVariables();
					if (lvars.length != rvars.length) {
						notEqual();
					}
					te.enqueueWalker(EndScope.INSTANCE);
					te.enqueueWalker(new TermEq(llet.getSubTerm(), rlet.getSubTerm()));
					final Term[] lvals = llet.getValues();
					final Term[] rvals = rlet.getValues();
					for (int i = 0; i < lvars.length; ++i) {
						te.enqueueWalker(new AddRenaming(lvars[i], rvars[i]));
						te.enqueueWalker(new TermEq(lvals[i], rvals[i]));
					}
					// te.enqueueWalker(BeginScope.INSTANCE);
					te.beginScope();
				} else if (mLhs instanceof QuantifiedFormula) {
					final QuantifiedFormula lq = (QuantifiedFormula) mLhs;
					final QuantifiedFormula rq = (QuantifiedFormula) mRhs;
					if (lq.getQuantifier() != rq.getQuantifier()) {
						notEqual();
					}
					final TermVariable[] lv = lq.getVariables();
					final TermVariable[] rv = rq.getVariables();
					if (lv.length != rv.length) {
						notEqual();
					}
					te.enqueueWalker(EndScope.INSTANCE);
					te.beginScope();
					for (int i = 0; i < lv.length; ++i) {
						if (lv[i] != rv[i]) {
							if (lv[i].getSort() != rv[i].getSort()) {
								notEqual();
							}
							te.addRenaming(lv[i], rv[i]);
						}
					}
					te.enqueueWalker(new TermEq(lq.getSubformula(), rq.getSubformula()));
				} else if (mLhs instanceof TermVariable) {
					final TermVariable lv = (TermVariable) mLhs;
					final TermVariable rv = (TermVariable) mRhs;
					if (!te.checkRenaming(lv, rv)) {
						notEqual();
					}
				} // Term case switch
			}
		}
	}

	private final static class ArrayEq implements Walker {

		private final Object[] mLhs, mRhs;

		public ArrayEq(Object[] lhs, Object[] rhs) {
			mLhs = lhs;
			mRhs = rhs;
		}

		private final void notEqual() {
			throw new NotEq();
		}

		@Override
		public void walk(NonRecursive engine) {
			final TermEquivalence te = (TermEquivalence) engine;
			if (mLhs != mRhs) {
				if (mLhs.getClass() != mRhs.getClass()) {
					// Cannot be equal
					notEqual();
				}
				if (mLhs.length != mRhs.length) {
					notEqual();
				}
				for (int i = 0; i < mLhs.length; ++i) {
					if (mLhs[i] == mRhs[i]) {
						continue;
					}
					if (mLhs[i] instanceof Term && mRhs[i] instanceof Term) {
						te.enqueueWalker(new TermEq((Term) mLhs[i], (Term) mRhs[i]));
					} else if (mLhs[i] instanceof Object[] && mRhs[i] instanceof Object[]) {
						te.enqueueWalker(new ArrayEq((Object[]) mLhs[i], (Object[]) mRhs[i]));
					} else {
						if (!mLhs[i].equals(mRhs[i])) {
							notEqual();
						}
					}
				}
			}
		}
	}
	
	/**
	 * Returns true if the terms are equivalent. 
	 * @param lhs the left hand side term.
	 * @param rhs the right hand side term.
	 * @return true if the terms are equivalent modulo variable renaming.
	 */
	public boolean equal(Term lhs, Term rhs) {
		try {
			run(new TermEq(lhs, rhs));
			return true;
		} catch (final NotEq ignored) {
			reset();
			return false;
		}
	}
	
}
