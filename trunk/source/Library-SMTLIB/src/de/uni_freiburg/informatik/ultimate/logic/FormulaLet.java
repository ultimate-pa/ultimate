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
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Compute the common-subexpression-elimination (cse) form of a term.  A term is
 * in cse form if all nodes with an out-degree of at least 1 and an in-degree of
 * at least 2 are eliminated, i.e., factored out into a let.
 * @author hoenicke
 */
public class FormulaLet extends NonRecursive {
	private final ArrayList<Map<Term, TermInfo>> mVisited = new ArrayList<>();
	private final ArrayList<Set<TermVariable>> mScopes = new ArrayList<>();
	private final ArrayDeque<Term> mResultStack = new ArrayDeque<>();
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

	private int findScope(final Term term) {
		final TermVariable[] tvs = term.getFreeVars();
		for (int scopeNr = mScopes.size() - 1; scopeNr >= 0; scopeNr--) {
			if (mScopes.get(scopeNr) == null) {
				return scopeNr;
			}
			for (final TermVariable tv : tvs) {
				if (mScopes.get(scopeNr).contains(tv)) {
					return scopeNr;
				}
			}
		}
		throw new AssertionError("no scope");
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
		enqueueLetter(input);
		run();
		final Term result = mResultStack.removeLast();
		assert mResultStack.size() == 0 && mVisited.size() == 0;
		assert new TermEquivalence().equal(
				new FormulaUnLet().unlet(result), input);
		return result;
	}

	/**
	 * For the initial formula and for each named term, a new scope for term infos
	 * is created (mVisited). It then creates a TermInfo for the term, which is
	 * walked first to collect all information about the term and its subterms.
	 * After collecting all info, the the term is transformed. to a letted term.
	 * Finally, the visited scope that was initially added is removed again.
	 */
	public void enqueueLetter(final Term term) {
		if (term instanceof TermVariable || term instanceof ConstantTerm) {
			mResultStack.addLast(term);
			return;
		}
		final Map<Term, TermInfo> newScope = new HashMap<>();
		mScopes.add(null);
		mVisited.add(newScope);
		final TermInfo info = new TermInfo(term);
		enqueueWalker(new ScopeRemover());
		enqueueWalker(new Transformer(info));
		enqueueWalker(new MarkLet(info));
		enqueueWalker(new CollectInfo(term, info));
	}

	/**
	 * Check if this term has a :named annotation.
	 */
	private static boolean isNamed(final AnnotatedTerm at) {
		return (at.getAnnotations().length == 1 && at.getAnnotations()[0].getKey().equals(":named"));
	}

	/**
	 * Check if this term is a :pattern annotation.
	 */
	private static boolean isPattern(final Term subterm) {
		if (subterm instanceof AnnotatedTerm) {
			final AnnotatedTerm at = (AnnotatedTerm) subterm;
			for (final Annotation annot : at.getAnnotations()) {
				if (!annot.getKey().equals(":pattern")) {
					return false;
				}
			}
			return true;
		}
		return false;
	}

	public static boolean bindsVariable(final Term parent, final Term child) {
		final HashSet<TermVariable> parentVars = new HashSet<>(Arrays.asList(parent.getFreeVars()));
		for (final TermVariable tv : child.getFreeVars()) {
			if (!parentVars.contains(tv)) {
				return true;
			}
		}
		return false;
	}

	public void addTransformScope(final TermVariable[] vars, final Map<Term, TermInfo> scope) {
		enqueueWalker(new ScopeRemover());
		mScopes.add(new HashSet<>(Arrays.asList(vars)));
		mVisited.add(scope);
	}

	/**
	 * Visit a child of the current term.
	 *
	 * @param let  The formula let environment.
	 * @param term The child term to visit.
	 */
	public void visitChild(final Term term) {
		// don't let term variables or constant terms
		if (term instanceof TermVariable || term instanceof ConstantTerm) {
			return;
		}
		// don't let function applications without arguments (constants)
		if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getParameters().length == 0) {
			return;
		}

		// check if term info exists
		final Map<Term, TermInfo> scopedInfos = mVisited.get(findScope(term));
		TermInfo child = scopedInfos.get(term);
		if (child == null) {
			// create new term info and visit the child recursively.
			child = new TermInfo(term);
			scopedInfos.put(term, child);
			enqueueWalker(new CollectInfo(term, child));
		} else {
			// already visited, just count the number of predecessors.
			child.mCount++;
		}
	}

	public Map<Term, TermInfo> newScope(final TermVariable[] vars) {
		final HashSet<TermVariable> varSet = new HashSet<>(Arrays.asList(vars));
		final Map<Term, TermInfo> newScope = new HashMap<>();
		mScopes.add(varSet);
		mVisited.add(newScope);
		enqueueWalker(new ScopeRemover());
		return newScope;
	}

	public final static class ScopeRemover implements Walker {
		@Override
		public void walk(final NonRecursive engine) {
			final FormulaLet let = (FormulaLet) engine;
			final int scopeNr = let.mScopes.size() - 1;
			let.mScopes.remove(scopeNr);
			let.mVisited.remove(scopeNr);
		}
	}

	/**
	 * This class collects informations for a term and is also a walker. As a walker it will just compute the
	 * predecessor counter (or occurrence counter).
	 */
	private final static class TermInfo {
		/**
		 * The term for which the term info is about.
		 */
		final Term mTerm;
		/**
		 * How many predecessors does this Term have?
		 */
		int                 mCount;
		/**
		 * How many times was this Term already visited in transform.
		 */
		int                 mSeen;
		/**
		 * The TermInfo for all sub terms that should be letted at this term. This is a
		 * list of list of terms to record the dependency relation between lets. If a
		 * letted term .cse1 uses a letted term .cse2 in its definition, the term .cse2
		 * must come before .cse1 in an earlier list.
		 */
		ArrayDeque<ArrayList<TermInfo>> mLettedTerms;
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
		/**
		 * The sub scopes in case this is a quantifier, lambda term or match term.
		 */
		Map<Term, TermInfo>[] mScopes;

		public TermInfo(final Term term) {
			mTerm = term;
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
				// we can use mParent, since we know there is a single predecessor and we
				// already called mergeParent
				// on it.
				info = info.mParent;
				// This has no parent -> no let.
				if (info == null) {
					return false;
				}
				// If we leave the scope of our variables, we cannot let.
				if (bindsVariable(info.mTerm, mTerm)) {
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
	}

	public static class CollectInfo implements Walker {
		Term mTerm;
		TermInfo mInfo;

		public CollectInfo(final Term term, final TermInfo info) {
			mTerm = term;
			mInfo = info;
		}

		@SuppressWarnings("unchecked")
		@Override
		public void walk(final NonRecursive walker) {
			final FormulaLet let = (FormulaLet) walker;
			if (mTerm instanceof AnnotatedTerm) {
				final AnnotatedTerm annotTerm = (AnnotatedTerm) mTerm;
				// Named terms are not counted. They are letted separately.
				if (!isNamed(annotTerm)) {
					// walk the main subterm
					let.visitChild(annotTerm.getSubterm());

					// walk all subterms occuring in the annotation
					// we use a small todo stack here in case the annotation contains nested arrays.
					final ArrayDeque<Object> todo = new ArrayDeque<>();
					for (final Annotation annot : annotTerm.getAnnotations()) {
						if (annot.getValue() != null) {
							todo.add(annot.getValue());
						}
					}
					while (!todo.isEmpty()) {
						final Object value = todo.removeLast();
						if (value instanceof Term) {
							let.visitChild((Term) value);
						} else if (value instanceof Object[]) {
							for (final Object elem : (Object[]) value) {
								todo.add(elem);
							}
						}
					}
				}
			} else if (mTerm instanceof ApplicationTerm) {
				final ApplicationTerm term = (ApplicationTerm) mTerm;
				final Term[] args = term.getParameters();
				for (final Term t : args) {
					let.visitChild(t);
				}
			} else if (mTerm instanceof LambdaTerm) {
				final LambdaTerm lambda = (LambdaTerm) mTerm;
				mInfo.mScopes = new Map[] { let.newScope(lambda.getVariables()) };
				let.visitChild(lambda.getSubterm());
			} else if (mTerm instanceof QuantifiedFormula) {
				final QuantifiedFormula quant = (QuantifiedFormula) mTerm;
				mInfo.mScopes = new Map[] { let.newScope(quant.getVariables()) };
				if (isPattern(quant.getSubformula())) {
					let.visitChild(((AnnotatedTerm) quant.getSubformula()).getSubterm());
				} else {
					let.visitChild(quant.getSubformula());
				}
			} else if (mTerm instanceof MatchTerm) {
				final MatchTerm match = (MatchTerm) mTerm;
				final int numCases = match.getCases().length;
				mInfo.mScopes = new Map[numCases];
				for (int i = numCases - 1; i >= 0; i--) {
					let.enqueueWalker(new CollectMatchCase(match, mInfo, i));
				}
				let.visitChild(match.getDataTerm());
			} else {
				throw new AssertionError();
			}
		}
	}

	public static class CollectMatchCase implements Walker {
		MatchTerm mTerm;
		TermInfo mInfo;
		int mCaseNr;

		public CollectMatchCase(final MatchTerm term, final TermInfo info, final int caseNr) {
			mTerm = term;
			mInfo = info;
			mCaseNr = caseNr;
		}

		@Override
		public void walk(final NonRecursive walker) {
			final FormulaLet let = (FormulaLet) walker;
			mInfo.mScopes[mCaseNr] = let.newScope(mTerm.getVariables()[mCaseNr]);
			let.visitChild(mTerm.getCases()[mCaseNr]);
		}
	}

	static class Converter implements Walker {
		Term mTerm;

		public Converter(final Term term) {
			mTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final FormulaLet let = (FormulaLet) engine;
			final Term term = mTerm;
			final Map<Term, TermInfo> scopeInfos = let.mVisited.get(let.findScope(term));
			final TermInfo info = scopeInfos.get(term);
			if (info == null) {
				let.mResultStack.addLast(term);
			} else if (info.mSubst != null) {
				let.mResultStack.addLast(info.mSubst);
			} else {
				let.enqueueWalker(new Transformer(info));
			}
		}
	}

	public static class TransformMatchCase implements Walker {
		MatchTerm mTerm;
		TermInfo mInfo;
		int mCaseNr;

		public TransformMatchCase(final MatchTerm term, final TermInfo info, final int caseNr) {
			mTerm = term;
			mInfo = info;
			mCaseNr = caseNr;
		}

		@Override
		public void walk(final NonRecursive walker) {
			// TODO
			final FormulaLet let = (FormulaLet) walker;
			let.addTransformScope(mTerm.getVariables()[mCaseNr], mInfo.mScopes[mCaseNr]);
			let.enqueueWalker(new Converter(mTerm.getCases()[mCaseNr]));
		}
	}

	/**
	 * This transforms the term into a letted term and puts it on the result stack. It is called by the converter class
	 * that determines when the term needs to be build, e.g. letted sub terms are only build when the let is going to be
	 * constructed.
	 */
	static class Transformer implements Walker {
		TermInfo mTermInfo;

		/**
		 * Create walker to transform the term into a letted term.
		 *
		 * @param parent
		 *            The predecessor, or the common ancestor term where the let is placed.
		 * @param isCounted
		 *            If this is false, we just create a copy of this term, because it could not be letted for some
		 *            reasons. We only count the last copy.
		 */
		public Transformer(final TermInfo parent) {
			mTermInfo = parent;
		}

		public void enqueueBuildLetTerms(final FormulaLet let) {
			for (final ArrayList<TermInfo> letList: mTermInfo.mLettedTerms) {
				assert !letList.isEmpty();
				final TermVariable[] tvs = new TermVariable[letList.size()];
				let.enqueueWalker(new BuildLetTerm(tvs));
				int i = 0;
				for (final TermInfo info : letList) {
					assert info.mSubst != null;
					tvs[i++] = info.mSubst;
					let.enqueueWalker(new Transformer(info));
				}
			}
		}

		@Override
		public void walk(final NonRecursive engine) {
			final FormulaLet let = ((FormulaLet) engine);
			final Term term = mTermInfo.mTerm;

			enqueueBuildLetTerms(let);

			if (term instanceof LambdaTerm) {
				final LambdaTerm lambda = (LambdaTerm) term;
				// enqueue the final walker that rebuilds the quantified term again.
				let.enqueueWalker(new BuildLambda(lambda));
				// add the stored scope for the subterm
				let.addTransformScope(lambda.getVariables(), mTermInfo.mScopes[0]);
				// enqueue a new letter for the sub formula.
				let.enqueueWalker(new Converter(lambda.getSubterm()));
			} else if (term instanceof QuantifiedFormula) {
				// Quantified formulas are handled by a completely new letter.
				final QuantifiedFormula quant = (QuantifiedFormula) term;
				// enqueue the final walker that rebuilds the quantified term again.
				let.enqueueWalker(new BuildQuantifier(quant));
				if (isPattern(quant.getSubformula())) {
					// avoid separating a pattern annotation from its quantifier. We do not let the
					// terms in the pattern annotation
					final AnnotatedTerm at = (AnnotatedTerm) quant.getSubformula();
					// enqueue the final walker that rebuilds the annotated term again.
					let.enqueueWalker(new BuildAnnotatedTerm(at));
					// recursively walk the annotation and push the contained terms.
					let.addTransformScope(quant.getVariables(), mTermInfo.mScopes[0]);
					let.enqueueWalker(new Converter(at.getSubterm()));
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
					let.addTransformScope(quant.getVariables(), mTermInfo.mScopes[0]);
					let.enqueueWalker(new Converter(quant.getSubformula()));
				}
			} else if (term instanceof AnnotatedTerm) {
				final AnnotatedTerm at = (AnnotatedTerm) term;
				// enqueue the final walker that rebuilds the annotated term again.
				let.enqueueWalker(new BuildAnnotatedTerm(at));
				if (isNamed(at)) {
					// Named terms are special and are handled by a completely new letter (they must not contain
					// variables).
					let.enqueueLetter(at.getSubterm());
				} else {
					// recursively walk the annotation and convert the contained terms.
					let.enqueueWalker(new Converter(at.getSubterm()));
					final ArrayDeque<Object> todo = new ArrayDeque<>();
					for (final Annotation annot : at.getAnnotations()) {
						if (annot.getValue() != null) {
							todo.add(annot.getValue());
						}
					}
					while (!todo.isEmpty()) {
						final Object value = todo.removeLast();
						if (value instanceof Term) {
							let.enqueueWalker(new Converter((Term) value));
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
					let.enqueueWalker(new Converter(params[i]));
				}
			} else if (term instanceof MatchTerm) {
				// enqueue the final walker that rebuilds the application term.
				final MatchTerm matchTerm = (MatchTerm) term;
				let.enqueueWalker(new BuildMatchTerm(matchTerm));
				// recursively convert the arguments.
				final Term[] cases = matchTerm.getCases();
				for (int i = cases.length - 1; i >= 0; i--) {
					let.enqueueWalker(new TransformMatchCase(matchTerm, mTermInfo, i));
				}
				let.enqueueWalker(new Converter(matchTerm.getDataTerm()));
			} else {
				// everything else is converted to itself
				let.mResultStack.addLast(term);
			}
		}
	}

	/**
	 * This class checks if there are sub terms that need to be letted. In that case we need to transform the sub terms
	 * and enqueue a BuildLetTerm that will finally add the let term.
	 */
	static class CollectLets implements Walker {
		final TermInfo mTermInfo;
		public CollectLets(final TermInfo parent) {
			mTermInfo = parent;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final List<TermInfo> lettedTerms = mTermInfo.mLettedTerms.getFirst();
			if (lettedTerms.isEmpty()) {
				// no terms want to be letted by us.
				mTermInfo.mLettedTerms.removeFirst();
				return;
			}
			final FormulaLet let = ((FormulaLet) engine);
			// Collecting the let definitions may create new letted terms so we need to run
			// again.
			let.enqueueWalker(this);
			mTermInfo.mLettedTerms.addFirst(new ArrayList<>());

			// now mark the lets in the let definitions.
			for (final TermInfo ti : lettedTerms) {
				let.enqueueWalker(new MarkLet(ti));
			}
		}
	}

	/**
	 * Add a let term around the term on the result stack using the let values also
	 * from the result stack and put the let term back onto the result stack.
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
	 * This tells each term about all of its parents and uses this to determine the
	 * let position for each term.
	 */
	static class AddParent implements Walker {
		TermInfo mParent;
		Term mTerm;

		public AddParent(final TermInfo parent, final Term term) {
			mParent = parent;
			mTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final FormulaLet let = ((FormulaLet) engine);
			final Term child = mTerm;
			final Map<Term, TermInfo> scopeInfos = let.mVisited.get(let.findScope(child));
			final TermInfo info = scopeInfos.get(child);
			if (info == null) {
				return;
			}
			if (info.mParent == null) {
				// we don't have a parent yet, set mParent to parent.
				info.mParent = mParent;
				info.mPDepth = mParent.mPDepth + 1;
				if (info.mSubst == null && !(child instanceof LambdaTerm)
						&& (let.mFilter == null || let.mFilter.isLettable(child)) && info.shouldBuildLet()) {
					// this will be letted, so create a new term variable for it.
					final Term t = info.mTerm;
					info.mSubst = t.getTheory().createTermVariable(".cse" + let.mCseNum++, t.getSort());
				}
			}
			info.mSeen++;
			if (info.mSeen == info.mCount) {
				// when we have visited all parents we start visiting the children.

				// merge parents, so that mParent points to the common ancestor of all parents.
				// we only have to call it on the last one.
				info.mergeParent(mParent);

				if (info.mSubst == null) {
					// if the subterm is not substituted, mark the subterm now.
					let.enqueueWalker(new MarkLet(info));
				} else {
					// otherwise add the subterm to the letted term of its parent.

					// Usually the let position is the common parent,
					// but if some ancestor occurs several times without being letted, we need to
					// move it to its ancestor to avoid creating the let multiple times.
					TermInfo ancestor = info.mParent;
					TermInfo letPos = ancestor;
					while (ancestor != null && ancestor.mSubst == null) {
						if (ancestor.mParent != null && bindsVariable(ancestor.mParent.mTerm, child)) {
							// the ancestors' parent binds some of the variables in child, so letPos must
							// stay below ancestors' parent.
							break;
						}
						if (ancestor.mCount > 1) {
							// ancestor occurs several times.
							// let position is the common parent of this ancestor.
							letPos = ancestor.mParent;
						}
						ancestor = ancestor.mParent;
					}
					// Tell our ancestor, that he needs to let us
					letPos.mLettedTerms.getFirst().add(info);
				}
			}
		}
	}

	public static class AddParentMatchCase implements Walker {
		MatchTerm mTerm;
		TermInfo mInfo;
		int mCaseNr;

		public AddParentMatchCase(final MatchTerm term, final TermInfo info, final int caseNr) {
			mTerm = term;
			mInfo = info;
			mCaseNr = caseNr;
		}

		@Override
		public void walk(final NonRecursive walker) {
			final FormulaLet let = (FormulaLet) walker;
			let.addTransformScope(mTerm.getVariables()[mCaseNr], mInfo.mScopes[mCaseNr]);
			let.enqueueWalker(new AddParent(mInfo, mTerm.getCases()[mCaseNr]));
		}
	}

	/**
	 * This transforms the term into a letted term and puts it on the result stack.
	 * It is called by the converter class that determines when the term needs to be
	 * build, e.g. letted sub terms are only build when the let is going to be
	 * constructed.
	 */
	static class MarkLet implements Walker {
		TermInfo mTermInfo;

		/**
		 * Create walker to transform the term into a letted term.
		 *
		 * @param parent    The predecessor, or the common ancestor term where the let
		 *                  is placed.
		 * @param isCounted If this is false, we just create a copy of this term,
		 *                  because it could not be letted for some reasons. We only
		 *                  count the last copy.
		 */
		public MarkLet(final TermInfo parent) {
			mTermInfo = parent;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final FormulaLet let = ((FormulaLet) engine);
			final Term term = mTermInfo.mTerm;
			// Enqueue the walker that will collect the let definitions later so that they
			// are collected at the right position.
			mTermInfo.mLettedTerms = new ArrayDeque<>();
			mTermInfo.mLettedTerms.addFirst(new ArrayList<>());
			let.enqueueWalker(new CollectLets(mTermInfo));

			if (term instanceof LambdaTerm) {
				final LambdaTerm lambda = (LambdaTerm) term;
				// add the stored scope for the subterm
				let.addTransformScope(lambda.getVariables(), mTermInfo.mScopes[0]);
				// enqueue a new letter for the sub formula.
				let.enqueueWalker(new AddParent(mTermInfo, lambda.getSubterm()));
			} else if (term instanceof QuantifiedFormula) {
				// Quantified formulas are handled by a completely new letter.
				final QuantifiedFormula quant = (QuantifiedFormula) term;
				if (isPattern(quant.getSubformula())) {
					// avoid separating a pattern annotation from its quantifier. We do not let the
					// terms in the pattern annotation
					final AnnotatedTerm at = (AnnotatedTerm) quant.getSubformula();
					// recursively walk the annotation and push the contained terms.
					let.addTransformScope(quant.getVariables(), mTermInfo.mScopes[0]);
					let.enqueueWalker(new AddParent(mTermInfo, at.getSubterm()));
				} else {
					// enqueue a new letter for the sub formula.
					let.addTransformScope(quant.getVariables(), mTermInfo.mScopes[0]);
					let.enqueueWalker(new AddParent(mTermInfo, quant.getSubformula()));
				}
			} else if (term instanceof AnnotatedTerm) {
				final AnnotatedTerm at = (AnnotatedTerm) term;
				// Named terms are special and are handled by a completely new letter (they must
				// not contain variables).
				if (!isNamed(at)) {
					// recursively walk the annotation and convert the contained terms.
					let.enqueueWalker(new AddParent(mTermInfo, at.getSubterm()));
					final ArrayDeque<Object> todo = new ArrayDeque<>();
					for (final Annotation annot : at.getAnnotations()) {
						if (annot.getValue() != null) {
							todo.add(annot.getValue());
						}
					}
					while (!todo.isEmpty()) {
						final Object value = todo.removeLast();
						if (value instanceof Term) {
							let.enqueueWalker(new AddParent(mTermInfo, (Term) value));
						} else if (value instanceof Object[]) {
							for (final Object elem : (Object[]) value) {
								todo.add(elem);
							}
						}
					}
				}
			} else if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				// recursively walk the arguments.
				final Term[] params = appTerm.getParameters();
				for (int i = params.length - 1; i >= 0; i--) {
					let.enqueueWalker(new AddParent(mTermInfo, params[i]));
				}
			} else if (term instanceof MatchTerm) {
				final MatchTerm matchTerm = (MatchTerm) term;
				// recursively convert the arguments.
				final Term[] cases = matchTerm.getCases();
				for (int i = cases.length - 1; i >= 0; i--) {
					let.enqueueWalker(new AddParentMatchCase(matchTerm, mTermInfo, i));
				}
				let.enqueueWalker(new AddParent(mTermInfo, matchTerm.getDataTerm()));
			} else {
				// everything else is converted to itself
				let.mResultStack.addLast(term);
			}
		}
	}
}
