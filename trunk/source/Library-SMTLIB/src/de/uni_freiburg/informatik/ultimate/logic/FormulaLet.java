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

	public FormulaLet(final LetFilter filter) {
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
		mVisited = new ArrayDeque<>();
		mResultStack = new ArrayDeque<>();
		run(new Letter(input));
		final Term result = mResultStack.removeLast();
		assert mResultStack.size() == 0 && mVisited.size() == 0;
		assert new TermEquivalence().equal(
				new FormulaUnLet().unlet(result), input);
		mResultStack = null;
		mVisited = null;
		return result;
	}

	/**
	 * This walker converts a term into a letted term.
	 *
	 * For the initial formula and for each quantifier, a new scope for term infos is created (mVisited).
	 * It then creates a TermInfo for the term, which is walked first to collect all information about the term and its
	 * subterms. After collecting all info, the the term is transformed. to a letted term. Finally, the visited scope
	 * that was initially added is removed again.
	 */
	static class Letter implements Walker {
		final Term mTerm;
		public Letter(final Term term) {
			mTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
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
				public void walk(final NonRecursive engine) {
					((FormulaLet) engine).mVisited.removeLast();
				}
			});
			engine.enqueueWalker(new Transformer(info, true));
			engine.enqueueWalker(info);
		}
	}

	/**
	 * This class collects informations for a term and is also a walker. As a walker it will just compute the
	 * predecessor counter (or occurrence counter).
	 */
	private final static class TermInfo extends TermWalker {
		/**
		 * How many predecessors does this Term have?
		 */
		int                 mCount;
		/**
		 * How many times was this Term already visited in transform.
		 */
		int                 mSeen;
		/**
		 * The TermInfo for all sub terms that should be letted at this term.
		 */
		ArrayList<TermInfo> mLettedTerms;
		/**
		 * If this term is letted, this is the term variable it is letted to.
		 */
		TermVariable        mSubst;
		/**
		 * If this term is letted, this is the term that will build the let, i.e., the nearest common parent.
		 */
		TermInfo            mParent;
		/**
		 * The length of the mParent list if you read it as linked list. This is used to quickly find a common parent.
		 * This is always equal to {@code mParent.mPDepth + 1}.
		 */
		int                 mPDepth;
		public TermInfo(final Term term) {
			super(term);
			mCount = 1;
		}

		/**
		 * Should we build a let for this term. This is the case if this term occurs several times, or if its single
		 * predecessor cannot be letted and occurs several times.
		 *
		 * @return
		 */
		public boolean shouldBuildLet() {
			TermInfo info = this;
			while (info.mCount == 1) {
				// we can use mParent, since we know there is a single predecessor and we already called mergeParent
				// on it.
				info = info.mParent;
				// This has no parent -> no let.
				if (info == null) {
					return false;
				}
				// parent is letted so this term really only occurs once.
				if (info.mSubst != null) {
					return false;
				}
			}
			return true;
		}

		/**
		 * Merge the mParent with parent, i.e. find the common parent of mParent and parent and update mParent.
		 *
		 * @param parent
		 *            The new parent that should be merged.
		 */
		public void mergeParent(TermInfo parent) {
			if (mParent == null) {
				// we don't have a parent yet, set mParent to parent.
				mParent = parent;
				mPDepth = parent.mPDepth + 1;
				return;
			}
			// Find the common parent. First make sure the depth is equal, then one can just compare mParent with
			// parent.
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
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			throw new InternalError("No TermInfo for ConstantTerm allowed");
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			// Named terms are not counted. They are letted separately.
			if (!isNamed(term)) {
				final FormulaLet let = (FormulaLet) walker;
				// walk the main subterm
				visitChild(let, term.getSubterm());

				// walk all subterms occuring in the annotation
				// we use a small todo stack here in case the annotation contains nested arrays.
				final ArrayDeque<Object> todo = new ArrayDeque<>();
				for (final Annotation annot : term.getAnnotations()) {
					if (annot.getValue() != null) {
						todo.add(annot.getValue());
					}
				}
				while (!todo.isEmpty()) {
					final Object value = todo.removeLast();
					if (value instanceof Term) {
						visitChild(let, (Term) value);
					} else if (value instanceof Object[]) {
						for (final Object elem : (Object[]) value) {
							todo.add(elem);
						}
					}
				}
			}
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			final Term[] args = term.getParameters();
			for (final Term t : args) {
				visitChild((FormulaLet) walker, t);
			}
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			throw new InternalError(
					"Let-Terms should not be in the formula anymore");
		}

		@Override
		public void walk(final NonRecursive walker, final LambdaTerm term) {
			// do not recurse into quantified formulas
			// this avoids problem with common terms containing free
			// variables

			// TODO: instead use scopes to distinguish variables?
			// ((FormulaLet) walker).visit(term.getSubformula(), this);
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			// do not recurse into quantified formulas
			// this avoids problem with common terms containing free
			// variables

			// TODO: instead use scopes to distinguish variables?
			//((FormulaLet) walker).visit(term.getSubformula(), this);
		}

		@Override
		public void walk(final NonRecursive walker, final MatchTerm term) {
			// TODO: same as quantified formula above
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			throw new InternalError("No TermInfo for TermVariable allowed");
		}

		/**
		 * Visit a child of the current term.
		 *
		 * @param let
		 *            The formula let environment.
		 * @param term
		 *            The child term to visit.
		 */
		public void visitChild(final FormulaLet let, final Term term) {
			// don't let term variables or constant terms
			if (term instanceof TermVariable
				|| term instanceof ConstantTerm) {
				return;
			}
			// don't let function applications without arguments (constants)
			if (term instanceof ApplicationTerm
				&& ((ApplicationTerm) term).getParameters().length == 0) {
				return;
			}

			// check if term info exists
			TermInfo child = let.mVisited.getLast().get(term);
			if (child == null) {
				// create new term info and visit the child recursively.
				child = new TermInfo(term);
				let.mVisited.getLast().put(term, child);
				let.enqueueWalker(child);
			} else {
				// already visited, just count the number of predecessors.
				child.mCount++;
			}
		}
	}

	/**
	 * This transforms the term into a letted term and puts it on the result stack. It is called by the converter class
	 * that determines when the term needs to be build, e.g. letted sub terms are only build when the let is going to be
	 * constructed.
	 */
	static class Transformer implements Walker {
		TermInfo mTermInfo;
		boolean mIsCounted;

		/**
		 * Create walker to transform the term into a letted term.
		 *
		 * @param parent
		 *            The predecessor, or the common ancestor term where the let is placed.
		 * @param isCounted
		 *            If this is false, we just create a copy of this term, because it could not be letted for some
		 *            reasons. We only count the last copy.
		 */
		public Transformer(final TermInfo parent, final boolean isCounted) {
			mTermInfo = parent;
			mIsCounted = isCounted;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final FormulaLet let = ((FormulaLet) engine);
			final Term term = mTermInfo.mTerm;
			if (mIsCounted) {
				// If this term is copied, it must not let anything, as the let would be duplicated.
				// Otherwise enqueue the walker that will build a let if this happens to become a parent for some
				// letted terms later.
				let.enqueueWalker(new BuildLet(mTermInfo));
				mTermInfo.mLettedTerms = new ArrayList<>();
			}
			if (term instanceof LambdaTerm) {
				// Lambda terms are handled by a completely new letter.
				final LambdaTerm lambda = (LambdaTerm) term;
				// enqueue the final walker that rebuilds the quantified term again.
				let.enqueueWalker(new BuildLambda(lambda));
				final Term sub = lambda.getSubterm();
				if (sub instanceof AnnotatedTerm) {
					// avoid separating a pattern annotation from its quantifier. We do not let the terms in the
					// pattern annotation
					final AnnotatedTerm at = (AnnotatedTerm) sub;
					// enqueue the final walker that rebuilds the annotated term again.
					let.enqueueWalker(new BuildAnnotatedTerm(at));
					// recursively walk the annotation and push the contained terms.
					let.enqueueWalker(new Letter(at.getSubterm()));
					final ArrayDeque<Object> todo = new ArrayDeque<>();
					for (final Annotation annot : at.getAnnotations()) {
						if (annot.getValue() != null) {
							todo.add(annot.getValue());
						}
					}
					while (!todo.isEmpty()) {
						final Object value = todo.removeFirst();
						if (value instanceof Term) {
							let.mResultStack.addLast((Term) value);
						} else if (value instanceof Object[]) {
							for (final Object elem : (Object[]) value) {
								todo.add(elem);
							}
						}
					}
				} else {
					// enqueue a new letter for the sub formula.
					let.enqueueWalker(new Letter(lambda.getSubterm()));
				}
			} else if (term instanceof QuantifiedFormula) {
				// Quantified formulas are handled by a completely new letter.
				final QuantifiedFormula quant = (QuantifiedFormula) term;
				// enqueue the final walker that rebuilds the quantified term again.
				let.enqueueWalker(new BuildQuantifier(quant));
				final Term sub = quant.getSubformula();
				if (sub instanceof AnnotatedTerm) {
					// avoid separating a pattern annotation from its quantifier. We do not let the
					// terms in the
					// pattern annotation
					final AnnotatedTerm at = (AnnotatedTerm) sub;
					// enqueue the final walker that rebuilds the annotated term again.
					let.enqueueWalker(new BuildAnnotatedTerm(at));
					// recursively walk the annotation and push the contained terms.
					let.enqueueWalker(new Letter(at.getSubterm()));
					final ArrayDeque<Object> todo = new ArrayDeque<>();
					for (final Annotation annot : at.getAnnotations()) {
						if (annot.getValue() != null) {
							todo.add(annot.getValue());
						}
					}
					while (!todo.isEmpty()) {
						final Object value = todo.removeFirst();
						if (value instanceof Term) {
							let.mResultStack.addLast((Term) value);
						} else if (value instanceof Object[]) {
							for (final Object elem : (Object[]) value) {
								todo.add(elem);
							}
						}
					}
				} else {
					// enqueue a new letter for the sub formula.
					let.enqueueWalker(new Letter(quant.getSubformula()));
				}
			} else if (term instanceof AnnotatedTerm) {
				final AnnotatedTerm at = (AnnotatedTerm) term;
				// enqueue the final walker that rebuilds the annotated term again.
				let.enqueueWalker(new BuildAnnotatedTerm(at));
				if (isNamed(at)) {
					// Named terms are special and are handled by a completely new letter (they must not contain
					// variables).
					let.enqueueWalker(new Letter(at.getSubterm()));
				} else {
					// recursively walk the annotation and convert the contained terms.
					let.enqueueWalker(new Converter(mTermInfo, at.getSubterm(), mIsCounted));
					final ArrayDeque<Object> todo = new ArrayDeque<>();
					for (final Annotation annot : at.getAnnotations()) {
						if (annot.getValue() != null) {
							todo.add(annot.getValue());
						}
					}
					while (!todo.isEmpty()) {
						final Object value = todo.removeLast();
						if (value instanceof Term) {
							let.enqueueWalker(new Converter(mTermInfo, (Term) value, mIsCounted));
						} else if (value instanceof Object[]) {
							for (final Object elem : (Object[]) value) {
								todo.add(elem);
							}
						}
					}
				}
			} else if (term instanceof ApplicationTerm) {
				// enqueue the final walker that rebuilds the application term.
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				let.enqueueWalker(new BuildApplicationTerm(appTerm));
				// recursively convert the arguments.
				final Term[] params = appTerm.getParameters();
				for (int i = params.length - 1; i >= 0; i--) {
					let.enqueueWalker(
						new Converter(mTermInfo, params[i], mIsCounted));
				}
			} else if (term instanceof MatchTerm) {
				// enqueue the final walker that rebuilds the application term.
				final MatchTerm matchTerm = (MatchTerm) term;
				let.enqueueWalker(new BuildMatchTerm(matchTerm));
				// recursively convert the arguments.
				final Term[] cases = matchTerm.getCases();
				for (int i = cases.length - 1; i >= 0; i--) {
					let.enqueueWalker(new Letter(cases[i]));
				}
				let.enqueueWalker(new Converter(mTermInfo, matchTerm.getDataTerm(), mIsCounted));
			} else {
				// everything else is converted to itself
				let.mResultStack.addLast(term);
			}
		}
	}

	/**
	 * This converts the term into a letted term and puts it on the result stack. This first checks if the term is that
	 * determines when the term needs to be build, e.g. letted sub terms are only build when the let is going to be
	 * constructed.
	 */
	static class Converter implements Walker {
		TermInfo mParent;
		Term mTerm;
		boolean mIsCounted;
		public Converter(final TermInfo parent, final Term term, final boolean isCounted) {
			mParent = parent;
			mTerm = term;
			mIsCounted = isCounted;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final FormulaLet let = ((FormulaLet) engine);
			final Term child = mTerm;
			final TermInfo info = let.mVisited.getLast().get(child);
			if (info == null) {
				let.mResultStack.addLast(child);
				return;
			}
			// merge parents, to find out where the let should be put into.
			info.mergeParent(mParent);
			if (info.shouldBuildLet() && info.mSubst == null
					&& !(child instanceof LambdaTerm)
					&& (let.mFilter == null || let.mFilter.isLettable(child))) {
				// this will be letted, so create a new term variable for it.
				final Term t = info.mTerm;
				info.mSubst = t.getTheory().createTermVariable(".cse" + let.mCseNum++, t.getSort());
			}
			if (mIsCounted && ++info.mSeen == info.mCount) {
				// this is the last time we visit this term. Now it is time to find our true parent that will let us.
				if (info.mSubst == null) {
					// we don't let this term, so just transform it (counted).
					let.enqueueWalker(new Transformer(info, true));
				} else {
					// We let this term. So the result is just the term variable.
					let.mResultStack.addLast(info.mSubst);

					// Usually the let position is the common parent,
					// but if some ancestor occurs several times without being letted, we need to move it to its
					// ancestor to avoid creating the let multiple times.
					TermInfo ancestor = info.mParent;
					TermInfo letPos = ancestor;
					while (ancestor != null && ancestor.mSubst == null) {
						if (ancestor.mCount > 1) {
							// ancestor occurs several times.
							// let position is the common parent of this ancestor.
							letPos = ancestor.mParent;
						}
						ancestor = ancestor.mParent;
					}
					// Tell our ancestor, that he needs to let us
					letPos.mLettedTerms.add(info);
				}
				return;
			}

			if (info.mSubst == null) {
				// we will not let the term, but it occurs several times. So we must not count
				// this visit.
				let.enqueueWalker(new Transformer(info, false));
			} else {
				// we will let the term, so this term is created to its term variable
				let.mResultStack.addLast(info.mSubst);
			}
		}
	}

	/**
	 * This class checks if there are sub terms that need to be letted. In that case we need to transform the sub terms
	 * and enqueue a BuildLetTerm that will finally add the let term.
	 */
	static class BuildLet implements Walker {
		final TermInfo mTermInfo;
		public BuildLet(final TermInfo parent) {
			mTermInfo = parent;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final List<TermInfo> lettedTerms = mTermInfo.mLettedTerms;
			if (lettedTerms.isEmpty()) {
				// no terms want to be letted by us.
				return;
			}
			final FormulaLet let = ((FormulaLet) engine);
			final TermVariable[] tvs = new TermVariable[lettedTerms.size()];
			// Building a let may create new letted terms so we need to run again.
			let.enqueueWalker(this);
			// Build the let term after we transformed the sub terms.
			let.enqueueWalker(new BuildLetTerm(tvs));
			int i = 0;
			// now transform the letted subterms; BuildLetTerm will collect them.
			for (final TermInfo ti : lettedTerms) {
				tvs[i++] = ti.mSubst;
				let.enqueueWalker(new Transformer(ti, true));
			}
			lettedTerms.clear();
		}
	}

	/**
	 * Add a let term around the term on the result stack using the let values also from the result stack and put the
	 * let term back onto the result stack.
	 */
	static class BuildLetTerm implements Walker {
		final TermVariable[] mVars;
		public BuildLetTerm(final TermVariable[] vars) {
			mVars = vars;
		}
		@Override
		public void walk(final NonRecursive engine) {
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

	/**
	 * Build an application term from the arguments on the result stack and the original function symbol and put the
	 * result on the result stack.
	 */
	static class BuildApplicationTerm implements Walker {
		final ApplicationTerm mOldTerm;
		public BuildApplicationTerm(final ApplicationTerm term) {
			mOldTerm = term;
		}

		public Term[] getTerms(final FormulaLet let, final Term[] oldArgs) {
			Term[] newArgs = oldArgs;
			for (int i = oldArgs.length - 1; i >= 0; i--) {
				final Term newTerm = let.mResultStack.removeLast();
				if (newTerm != oldArgs[i]) {
					if (newArgs == oldArgs) {
						newArgs = oldArgs.clone();
					}
					newArgs[i] = newTerm;
				}
			}
			return newArgs;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final FormulaLet let = (FormulaLet)engine;
			final Term[] newParams = getTerms(let, mOldTerm.getParameters());
			Term result = mOldTerm;
			if (newParams != mOldTerm.getParameters()) {
				final Theory theory = mOldTerm.getTheory();
				result = theory.term(mOldTerm.getFunction(), newParams);
			}
			let.mResultStack.addLast(result);
		}
	}

	/**
	 * Build a lambda term on the result stack and put the result on the result
	 * stack.
	 */
	static class BuildLambda implements Walker {
		final LambdaTerm mOldTerm;

		public BuildLambda(final LambdaTerm term) {
			mOldTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final FormulaLet let = (FormulaLet) engine;
			final Term newBody = let.mResultStack.removeLast();
			Term result = mOldTerm;
			if (newBody != mOldTerm.getSubterm()) {
				final Theory theory = mOldTerm.getTheory();
				result = theory.lambda(mOldTerm.getVariables(), newBody);
			}
			let.mResultStack.addLast(result);
		}
	}

	/**
	 * Build a quantifier around the term on the result stack and put the result on
	 * the result stack.
	 */
	static class BuildQuantifier implements Walker {
		final QuantifiedFormula mOldTerm;
		public BuildQuantifier(final QuantifiedFormula term) {
			mOldTerm = term;
		}
		@Override
		public void walk(final NonRecursive engine) {
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

	/**
	 * Build a match term using the terms on the result stack and put the result on the result stack.
	 */
	static class BuildMatchTerm implements Walker {
		final MatchTerm mOldTerm;

		public BuildMatchTerm(final MatchTerm term) {
			mOldTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final FormulaLet let = (FormulaLet) engine;
			final Term[] oldCases = mOldTerm.getCases();
			Term[] newCases = oldCases;
			for (int i = oldCases.length - 1; i >= 0; i--) {
				final Term caseTerm = let.mResultStack.removeLast();
				if (caseTerm != oldCases[i]) {
					if (newCases == oldCases) {
						newCases = oldCases.clone();
					}
					newCases[i] = caseTerm;
				}
			}
			final Term newDataTerm = let.mResultStack.removeLast();

			Term result = mOldTerm;
			if (newDataTerm != mOldTerm.getDataTerm() || newCases != oldCases) {
				final Theory theory = mOldTerm.getTheory();
				result = theory.match(newDataTerm, mOldTerm.getVariables(), newCases, mOldTerm.getConstructors());
			}
			let.mResultStack.addLast(result);
		}
	}

	/**
	 * Build an annotated term around the term on the result stack (and all term valued annotations also on result
	 * stack) and put the result on the result stack.
	 */
	static class BuildAnnotatedTerm implements Walker {
		final AnnotatedTerm mOldTerm;
		public BuildAnnotatedTerm(final AnnotatedTerm term) {
			mOldTerm = term;
		}

		private Object retrieveValue(final FormulaLet let, final Object old) {
			if (old instanceof Term) {
				return let.mResultStack.removeLast();
			} else if (old instanceof Object[]) {
				Object[] newArray = (Object[]) old;
				for (int i = newArray.length - 1; i >= 0; i--) {
					final Object oldValue = newArray[i];
					final Object newValue = retrieveValue(let, oldValue);
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
		public void walk(final NonRecursive engine) {
			final FormulaLet let = (FormulaLet)engine;
			Term result = mOldTerm;
			final Term newBody = let.mResultStack.removeLast();
			final Annotation[] oldAnnot = mOldTerm.getAnnotations();
			Annotation[] newAnnot = oldAnnot;
			for (int i = oldAnnot.length - 1; i >= 0; i--) {
				final Object oldValue = oldAnnot[i].getValue();
				final Object newValue = retrieveValue(let, oldValue);
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

	/**
	 * Check if this term has a :named annotation.
	 */
	private static boolean isNamed(final AnnotatedTerm at) {
		for (final Annotation a : at.getAnnotations()) {
			if (a.getKey().equals(":named")) {
				return true;
			}
		}
		return false;
	}
}
