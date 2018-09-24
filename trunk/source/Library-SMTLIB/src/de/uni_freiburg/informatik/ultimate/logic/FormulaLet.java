/*
 * Copyright (C) 2009-2012 University of Freiburg
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Compute the common-subexpression-elimination (cse) form of a term.  A term is
 * in cse form if all nodes with an out-degree of at least 1 and an in-degree of
 * at least 2 are eliminated, i.e., factored out into a let.
 * @author hoenicke
 */
public class FormulaLet extends NonRecursive {
	private ArrayDeque<Map<Term, TermInfo>> mVisited;
	private ArrayDeque<Term> mResultStack;
	private int mCseNum;
	private final LetFilter mFilter;
	
	public static interface LetFilter {
		public boolean isLettable(Term t);
	}
	
	public FormulaLet() {
		this(null);
	}

	public FormulaLet(LetFilter filter) {
		mFilter = filter;
	}
	/**
	 * Compute the cse form of a term.  Note that all lets will be removed from
	 * the input before computing the cse form.
	 * @param input The input term.
	 * @return A term in cse form that represents the same DAG than the input.
	 */
	public Term let(Term input) {
		input = new FormulaUnLet().unlet(input);
		mCseNum = 0;
		mVisited = new ArrayDeque<Map<Term,TermInfo>>();
		mResultStack = new ArrayDeque<Term>();
		run(new Letter(input));
		final Term result = mResultStack.removeLast();
		assert mResultStack.size() == 0 && mVisited.size() == 0;
		assert new TermEquivalence().equal(
				new FormulaUnLet().unlet(result), input);
		mResultStack = null;
		mVisited = null;
		return result;
	}
	
	static class Letter implements Walker {
		final Term mTerm;
		public Letter(Term term) {
			mTerm = term;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			if (mTerm instanceof TermVariable
				|| mTerm instanceof ConstantTerm) {
				((FormulaLet) engine).mResultStack.addLast(mTerm);
				return;
			}
			((FormulaLet) engine).mVisited.addLast(
					new HashMap<Term, FormulaLet.TermInfo>());
			final TermInfo info = new TermInfo(mTerm);
			((FormulaLet) engine).mVisited.getLast().put(mTerm, info);
			engine.enqueueWalker(new Walker() {
				@Override
				public void walk(NonRecursive engine) {
					((FormulaLet) engine).mVisited.removeLast();
				}
			});
			engine.enqueueWalker(new Transformer(info, true));
			engine.enqueueWalker(info);
		}
	}
	
	private final static class TermInfo extends TermWalker {
		int                 mCount;
		int                 mSeen;
		ArrayList<TermInfo> mLettedTerms;
		TermVariable        mSubst;
		TermInfo            mParent;
		int                 mPDepth;
		public TermInfo(Term term) {
			super(term);
			mCount = 1;
		}

		public boolean shouldBuildLet() {
			TermInfo info = this;
			while (info.mCount == 1) {
				info = info.mParent;
				if (info == null) {
					return false;
				}
				if (info.mSubst != null) {
					return false;
				}
			}
			return true;
		}
		
		public void mergeParent(TermInfo parent) {
			if (mParent == null) {
				mParent = parent;
				mPDepth = parent.mPDepth + 1;
				return;
			}
			while (mParent != parent) {
				if (parent.mPDepth == mParent.mPDepth) {
					parent = parent.mParent;
					mParent = mParent.mParent;
				} else if (parent.mPDepth > mParent.mPDepth) {
					parent = parent.mParent;
				} else {
					mParent = mParent.mParent;
				}
			}
			mPDepth = mParent.mPDepth + 1;
		}
		
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			throw new InternalError("No TermInfo for ConstantTerm allowed");
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			if (!isNamed(term)) {
				FormulaLet let = (FormulaLet) walker;
				visitChild(let, term.getSubterm());
				final ArrayDeque<Object> todo = new ArrayDeque<>();
				for (Annotation annot : term.getAnnotations()) {
					if (annot.getValue() != null) {
						todo.add(annot.getValue());
					}
				}
				while (!todo.isEmpty()) {
					Object value = todo.removeLast();
					if (value instanceof Term) {
						visitChild(let, (Term) value);
					} else if (value instanceof Object[]) {
						for (Object elem : (Object[]) value) {
							todo.add(elem);
						}
					}
				}
			}
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			final Term[] args = term.getParameters();
			for (final Term t : args) {
				visitChild((FormulaLet) walker, t);
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			throw new InternalError(
					"Let-Terms should not be in the formula anymore");
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			// do not recurse into quantified formulas
			// this avoids problem with common terms containing free
			// variables
			//((FormulaLet) walker).visit(term.getSubformula(), this);
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			throw new InternalError("No TermInfo for TermVariable allowed");
		}

		public void visitChild(FormulaLet let, Term term) {
			if (term instanceof TermVariable
				|| term instanceof ConstantTerm) {
				return;
			}
			if (term instanceof ApplicationTerm
				&& ((ApplicationTerm) term).getParameters().length == 0) {
				return;
			}
	
			TermInfo child = let.mVisited.getLast().get(term);
			if (child == null) {
				child = new TermInfo(term);
				let.mVisited.getLast().put(term, child);
				let.enqueueWalker(child);
			} else {
				child.mCount++;
			}
		}
	}
	
	static class Transformer implements Walker {
		TermInfo mTermInfo;
		boolean mIsCounted;
		public Transformer(TermInfo parent, boolean isCounted) {
			mTermInfo = parent;
			mIsCounted = isCounted;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			final FormulaLet let = ((FormulaLet) engine);
			final Term term = mTermInfo.mTerm;
			if (mIsCounted) {
				let.enqueueWalker(new BuildLet(mTermInfo));
				mTermInfo.mLettedTerms = new ArrayList<TermInfo>();
			}
			if (term instanceof QuantifiedFormula) {
				final QuantifiedFormula quant = (QuantifiedFormula) term;
				let.enqueueWalker(new BuildQuantifier(quant));
				let.enqueueWalker(new Letter(quant.getSubformula()));
			} else if (term instanceof AnnotatedTerm) {
				final AnnotatedTerm at = (AnnotatedTerm) term;
				let.enqueueWalker(new BuildAnnotatedTerm(at));
				if (isNamed(at)) {
					let.enqueueWalker(new Letter(at.getSubterm()));
				} else {
					let.enqueueWalker(new Converter(mTermInfo, at.getSubterm(), mIsCounted));
					final ArrayDeque<Object> todo = new ArrayDeque<>();
					for (Annotation annot : at.getAnnotations()) {
						if (annot.getValue() != null) {
							todo.add(annot.getValue());
						}
					}
					while (!todo.isEmpty()) {
						Object value = todo.removeLast();
						if (value instanceof Term) {
							let.enqueueWalker(new Converter(mTermInfo, (Term) value, mIsCounted));
						} else if (value instanceof Object[]) {
							for (Object elem : (Object[]) value) {
								todo.add(elem);
							}
						}
					}
				}
			} else if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				let.enqueueWalker(new BuildApplicationTerm(appTerm));
				final Term[] params = appTerm.getParameters();
				for (int i = params.length - 1; i >= 0; i--) {
					let.enqueueWalker(
						new Converter(mTermInfo, params[i], mIsCounted));
				}
			} else {
				let.mResultStack.addLast(term);
			}
		}
	}

	static class Converter implements Walker {
		TermInfo mParent;
		Term mTerm;
		boolean mIsCounted;
		public Converter(TermInfo parent, Term term, boolean isCounted) {
			mParent = parent;
			mTerm = term;
			mIsCounted = isCounted;
		}

		@Override
		public void walk(NonRecursive engine) {
			final FormulaLet let = ((FormulaLet) engine);
			final Term child = mTerm;
			final TermInfo info = let.mVisited.getLast().get(child);
			if (info == null) {
				let.mResultStack.addLast(child);
				return;
			}
			info.mergeParent(mParent);
			if (info.shouldBuildLet() && info.mSubst == null 
				&& (let.mFilter == null || let.mFilter.isLettable(child))) {
				final Term t = info.mTerm; 
				info.mSubst = t.getTheory().
					createTermVariable(".cse" + let.mCseNum++, t.getSort());
			}
			if (mIsCounted && ++info.mSeen == info.mCount) {
				if (info.mSubst == null) {
					let.enqueueWalker(new Transformer(info, true));
				} else {
					let.mResultStack.addLast(info.mSubst);
					TermInfo ancestor = info.mParent;
					TermInfo letPos = ancestor;
					while (ancestor != null && ancestor.mSubst == null) {
						if (ancestor.mCount > 1) {
							letPos = ancestor.mParent;
						}
						ancestor = ancestor.mParent;
					}
					letPos.mLettedTerms.add(info);
				}
				return;
			}
			
			if (info.mSubst == null) {
				let.enqueueWalker(new Transformer(info, false));
			} else {
				let.mResultStack.addLast(info.mSubst);
			}
		}
	}
	
	static class BuildLet implements Walker {
		final TermInfo mTermInfo;
		public BuildLet(TermInfo parent) {
			mTermInfo = parent;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			final List<TermInfo> lettedTerms = mTermInfo.mLettedTerms;
			if (lettedTerms.isEmpty()) {
				return;
			}
			final FormulaLet let = ((FormulaLet) engine);
			final TermVariable[] tvs = new TermVariable[lettedTerms.size()];
			let.enqueueWalker(this);
			let.enqueueWalker(new BuildLetTerm(tvs));
			int i = 0;
			for (final TermInfo ti : lettedTerms) {
				tvs[i++] = ti.mSubst;
				let.enqueueWalker(new Transformer(ti, true));
			}
			lettedTerms.clear();
		}
	}
	
	static class BuildLetTerm implements Walker {
		final TermVariable[] mVars;
		public BuildLetTerm(TermVariable[] vars) {
			mVars = vars;
		}
		@Override
		public void walk(NonRecursive engine) {
			final FormulaLet let = (FormulaLet)engine;
			final Term[] values = new Term[mVars.length];
			for (int i = 0; i < values.length; i++) {
				values[i] = let.mResultStack.removeLast();
			}
			final Term newBody = let.mResultStack.removeLast();
			final Theory theory = newBody.getTheory();
			final Term result = theory.let(mVars, values, newBody);
			let.mResultStack.addLast(result);
		}
	}

	static class BuildApplicationTerm implements Walker {
		final ApplicationTerm mOldTerm;
		public BuildApplicationTerm(ApplicationTerm term) {
			mOldTerm = term;
		}
		@Override
		public void walk(NonRecursive engine) {
			final FormulaLet let = (FormulaLet)engine;
			final Term[] newParams = let.getTerms(mOldTerm.getParameters());
			Term result = mOldTerm;
			if (newParams != mOldTerm.getParameters()) {
				final Theory theory = mOldTerm.getTheory();
				result = theory.term(mOldTerm.getFunction(), newParams);
			}
			let.mResultStack.addLast(result);
		}
	}

	static class BuildQuantifier implements Walker {
		final QuantifiedFormula mOldTerm;
		public BuildQuantifier(QuantifiedFormula term) {
			mOldTerm = term;
		}
		@Override
		public void walk(NonRecursive engine) {
			final FormulaLet let = (FormulaLet)engine;
			final Term newBody = let.mResultStack.removeLast();
			Term result = mOldTerm;
			if (newBody != mOldTerm.getSubformula()) {
				final Theory theory = mOldTerm.getTheory();
				if (mOldTerm.getQuantifier() == QuantifiedFormula.EXISTS) {
					result = theory.exists(mOldTerm.getVariables(), newBody);
				} else {
					result = theory.forall(mOldTerm.getVariables(), newBody);
				}
			}
			let.mResultStack.addLast(result);
		}
	}

	static class BuildAnnotatedTerm implements Walker {
		final AnnotatedTerm mOldTerm;
		public BuildAnnotatedTerm(AnnotatedTerm term) {
			mOldTerm = term;
		}

		private Object retrieveValue(FormulaLet let, Object old) {
			if (old instanceof Term) {
				return let.mResultStack.removeLast();
			} else if (old instanceof Object[]) {
				Object[] newArray = (Object[]) old;
				for (int i = newArray.length - 1; i >= 0; i--) {
					Object oldValue = newArray[i];
					Object newValue = retrieveValue(let, oldValue);
					if (oldValue != newValue) {
						if (newArray == old) {
							newArray = newArray.clone();
						}
						newArray[i] = newValue;
					}
				}
				return newArray;
			} else {
				return old;
			}
		}

		@Override
		public void walk(NonRecursive engine) {
			final FormulaLet let = (FormulaLet)engine;
			Term result = mOldTerm;
			final Term newBody = let.mResultStack.removeLast();
			Annotation[] oldAnnot = mOldTerm.getAnnotations();
			Annotation[] newAnnot = oldAnnot;
			for (int i = oldAnnot.length - 1; i >= 0; i--) {
				Object oldValue = oldAnnot[i].getValue();
				Object newValue = retrieveValue(let, oldValue);
				if (newValue != oldValue) {
					if (newAnnot == oldAnnot) {
						newAnnot = oldAnnot.clone();
					}
					newAnnot[i] = new Annotation(oldAnnot[i].getKey(), newValue);
				}
			}
			if (newBody != mOldTerm.getSubterm() || newAnnot != oldAnnot) {
				final Theory theory = mOldTerm.getTheory();
				result = theory.annotatedTerm(newAnnot, newBody);
			}
			let.mResultStack.addLast(result);
		}
	}

	private static boolean isNamed(AnnotatedTerm at) {
		for (final Annotation a : at.getAnnotations()) {
			if (a.getKey().equals(":named")) {
				return true;
			}
		}
		return false;
	}

	public Term[] getTerms(Term[] oldArgs) {
		Term[] newArgs = oldArgs;
		for (int i = oldArgs.length - 1; i >= 0; i--) {
			final Term newTerm = mResultStack.removeLast();
			if (newTerm != oldArgs[i]) {
				if (newArgs == oldArgs) {
					newArgs = oldArgs.clone();
				}
				newArgs[i] = newTerm;
			}
		}
		return newArgs;
	}
}
