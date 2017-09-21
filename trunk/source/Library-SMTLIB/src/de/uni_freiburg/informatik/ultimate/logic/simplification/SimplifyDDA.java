/*
 * Copyright (C) 2009-2013 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.logic.simplification;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.PushPopChecker;

/**
 * Simplify formulas, but keep their Boolean structure. Replace subformulas by true or false if this replacement leads
 * to an equivalent formula. Based on the paper "Small Formulas for Large Programms: On-Line Constraint Simplification
 * in Scalable Static Analysis" by Isil Dillig, Thomas Dillig and Alex Aiken. This implementation extends this approach
 * to formulas which are not in NNF, contain "=>" and "ite".
 *
 * The new implementation is DAG-based an non-recursive. We collect contexts
 *
 * @author Matthias Heizmann, Jochen Hoenicke, Markus Pomrehn
 *
 */
public class SimplifyDDA extends NonRecursive {

	private static class TermInfo {
		int mNumPredecessors;
		int mSeen;
		int mPrepared;
		Term[] mContext;
		Term mSimplified;

		@Override
		public String toString() {
			return "TermInfo[" + mNumPredecessors + "," + mSeen + "," + mPrepared
					+ (mContext == null ? "" : ",context:" + Arrays.toString(mContext))
					+ (mSimplified == null ? "" : "->" + mSimplified) + "]";
		}
	}

	HashMap<Term, TermInfo> mTermInfos;
	Term mResult;
	protected final Script mScript;
	final Term mTrue;
	final Term mFalse;
	protected final boolean mSimplifyRepeatedly;
	/**
	 * If asserting a term returns UNSAT, we use this flag to store that the context is inconsistent. The flag it set to
	 * false whenever we pop the context.
	 */
	protected boolean mInconsistencyOfContextDetected;

	/**
	 * This class counts the predecessors of every term to enable the next passes to determine whether we need to
	 * collect information.
	 *
	 * @author hoenicke
	 */
	private static class TermCounter implements Walker {
		protected Term mTerm;

		public TermCounter(Term term) {
			/* directly descend into not-terms as if the not is not there */
			while (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName() == "not") {
					term = appTerm.getParameters()[0];
				} else {
					break;
				}
			}
			mTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final SimplifyDDA simplifier = (SimplifyDDA) engine;
			TermInfo info = simplifier.mTermInfos.get(mTerm);
			if (info == null) {
				info = new TermInfo();
				simplifier.mTermInfos.put(mTerm, info);

				if (mTerm instanceof ApplicationTerm) {
					final ApplicationTerm appTerm = (ApplicationTerm) mTerm;
					final String connective = appTerm.getFunction().getName();

					if (connective == "ite" || connective == "and" || connective == "or" || connective == "=>") {
						for (final Term subTerm : appTerm.getParameters()) {
							engine.enqueueWalker(new TermCounter(subTerm));
						}
					}
				}
			}
			info.mNumPredecessors++;
		}
	}

	/**
	 * This class collects the contexts (for the context simplifier) in which a term occurs. It does not simplify the
	 * term.
	 *
	 * @author hoenicke
	 */
	private static class ContextCollector implements Walker {
		final boolean mNegated;
		final Term mTerm;
		ArrayDeque<Term> mContext;
		int mParamCtr;

		public ContextCollector(boolean negated, Term term, final ArrayDeque<Term> context) {
			/* directly descend into not-terms as if the not is not there */
			while (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName() == "not") {
					term = appTerm.getParameters()[0];
					negated ^= true;
				} else {
					break;
				}
			}
			mNegated = negated;
			mTerm = term;
			mContext = context;
			mParamCtr = 0;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final SimplifyDDA simplifier = (SimplifyDDA) engine;
			if (mParamCtr > 0) {
				walkNextParameter(simplifier);
				return;
			}
			final TermInfo info = simplifier.mTermInfos.get(mTerm);
			assert info != null;
			info.mSeen++;
			assert info.mSeen <= info.mNumPredecessors;
			if (info.mNumPredecessors > 1) {
				// merge context
				if (info.mContext == null) {
					info.mContext = mContext.toArray(new Term[mContext.size()]);
				} else {
					final HashSet<Term> oldContext = new HashSet<>(info.mContext.length);
					oldContext.addAll(Arrays.asList(info.mContext));
					final ArrayDeque<Term> newContext = new ArrayDeque<>(info.mContext.length);
					for (final Term t : mContext) {
						if (oldContext.contains(t)) {
							newContext.add(t);
						}
					}
					mContext = newContext;
					info.mContext = newContext.toArray(new Term[newContext.size()]);
				}
				if (info.mSeen < info.mNumPredecessors) {
					return;
				}
			}

			if (mTerm instanceof ApplicationTerm) {
				walkNextParameter(simplifier);
			}
		}

		public void walkNextParameter(final SimplifyDDA simplifier) {
			final ApplicationTerm appTerm = (ApplicationTerm) mTerm;
			final String connective = appTerm.getFunction().getName();
			final Term[] params = appTerm.getParameters();

			if (connective == "ite") {
				final Term cond = params[0];
				if (mParamCtr == 0) {
					simplifier.enqueueWalker(this);
					simplifier.enqueueWalker(new ContextCollector(false, cond, mContext));
				} else if (mParamCtr == 1) {
					mContext.push(cond);
					simplifier.enqueueWalker(this);
					simplifier.enqueueWalker(new ContextCollector(mNegated, params[1], mContext));
				} else if (mParamCtr == 2) {
					mContext.pop();
					mContext.push(Util.not(simplifier.mScript, cond));
					simplifier.enqueueWalker(this);
					simplifier.enqueueWalker(new ContextCollector(mNegated, params[2], mContext));
				} else if (mParamCtr == 3) { // NOCHECKSTYLE
					mContext.pop();
				}
				mParamCtr++;
			} else if (connective == "and" || connective == "or" || connective == "=>") {
				if (mParamCtr == 0) {
					for (int i = params.length - 1; i > 0; i--) {
						final Term sibling = simplifier.negateSibling(params[i], connective, i, params.length);
						mContext.push(sibling);
					}
					simplifier.enqueueWalker(this);
					simplifier.enqueueWalker(new ContextCollector(mNegated, params[mParamCtr], mContext));
				} else if (mParamCtr < params.length) {
					// The context contains:
					// param[len-1] ... param[mParamCtr]
					// simplify(param[mParamCtr-2])... simplify(param[0])
					// we need to replace param[mParamCtr]
					// by simplify(param[mParamCtr-1]).
					/*
					 * this is dangerous: the simplified formulas may depend on their context, therefore we cannot
					 * simply merge them. for (int i = 0; i < mParamCtr; i++) { mContext.pop(); } for (int i =
					 * mParamCtr-1; i >= 0; i--) { Term sibling = simplifier.negateSibling( params[i], connective, i,
					 * params.length); sibling = simplifier.createSimplify(sibling); mContext.push(sibling); }
					 */
					mContext.pop();
					simplifier.enqueueWalker(this);
					simplifier.enqueueWalker(new ContextCollector(mNegated, params[mParamCtr], mContext));
				} else {
					/*
					 * for (int i = 0; i < mParamCtr-1; i++) { mContext.pop(); }
					 */
				}
				mParamCtr++;
			}
		}
	}

	/**
	 * This class simplifies the terms in a post-order traversal. First we descend into children doing nothing. When
	 * getting back to the parent again we simplify it, provided it has more than one predecessor.
	 *
	 * @author hoenicke
	 */
	private static class PrepareSimplifier implements Walker {
		final Term mTerm;

		public PrepareSimplifier(final boolean negated, Term term) {
			/* directly descend into not-terms as if the not is not there */
			while (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName() == "not") {
					term = appTerm.getParameters()[0];
				} else {
					break;
				}
			}
			mTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final SimplifyDDA simplifier = (SimplifyDDA) engine;
			final TermInfo info = simplifier.mTermInfos.get(mTerm);
			if (info.mPrepared++ > 0) {
				return;
			}

			if (info.mNumPredecessors > 1) {
				engine.enqueueWalker(new StoreSimplified(mTerm));
				engine.enqueueWalker(new Simplifier(false, mTerm, info.mContext));
			}
			if (mTerm instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) mTerm;
				final String connective = appTerm.getFunction().getName();
				final Term[] params = appTerm.getParameters();

				if (connective == "ite" || connective == "and" || connective == "or" || connective == "=>") {
					for (int i = 0; i < params.length; i++) {
						engine.enqueueWalker(new PrepareSimplifier(false, params[i]));
					}
				}
			}
		}

		@Override
		public String toString() {
			return "PrepareSimplifier[" + mTerm + "]";
		}
	}

	private static class StoreSimplified implements Walker {
		Term mTerm;

		public StoreSimplified(final Term term) {
			mTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final SimplifyDDA simplifier = (SimplifyDDA) engine;
			final TermInfo info = simplifier.mTermInfos.get(mTerm);
			info.mSimplified = simplifier.popResult();
		}

		@Override
		public String toString() {
			return "StoreSimplified[" + mTerm + "]";
		}
	}

	private static class Simplifier implements Walker {
		final boolean mNegated;
		final Term mTerm;
		final Term[] mContext;
		int mParamCtr;
		Term[] mSimplifiedParams;

		public Simplifier(boolean negated, Term term, final Term[] context) {
			/* directly descend into not-terms as if the not is not there */
			while (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName() == "not") {
					term = appTerm.getParameters()[0];
					negated ^= true;
				} else {
					break;
				}
			}
			mNegated = negated;
			mTerm = term;
			mContext = context;
			mParamCtr = 0;
		}

		public Simplifier(boolean negated, Term term) {
			/* directly descend into not-terms as if the not is not there */
			while (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName() == "not") {
					term = appTerm.getParameters()[0];
					negated ^= true;
				} else {
					break;
				}
			}
			mNegated = negated;
			mTerm = term;
			mContext = null;
			mParamCtr = 0;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final SimplifyDDA simplifier = (SimplifyDDA) engine;
			if (mParamCtr > 0) {
				walkParam(simplifier);
				return;
			}
			if (mContext == null) {
				/* check for redundancy, then for info */
				final Redundancy red = simplifier.getRedundancy(mTerm);
				if (red != Redundancy.NOT_REDUNDANT) {
					if (red == Redundancy.NON_RELAXING) {
						simplifier.setResult(mNegated, simplifier.mFalse);
					} else {
						simplifier.setResult(mNegated, simplifier.mTrue);
					}
					return;
				}

				final TermInfo info = simplifier.mTermInfos.get(mTerm);
				if (info.mNumPredecessors > 1) {
					assert info.mSimplified != null;
					simplifier.setResult(mNegated, info.mSimplified);
					return;
				}
			}

			if (mContext != null) {
				simplifier.pushContext(mContext);

				/* check for redundancy */
				final Redundancy red = simplifier.getRedundancy(mTerm);
				if (red != Redundancy.NOT_REDUNDANT) {
					if (red == Redundancy.NON_RELAXING) {
						simplifier.setResult(mNegated, simplifier.mFalse);
					} else {
						simplifier.setResult(mNegated, simplifier.mTrue);
					}
					simplifier.popContext();
					return;
				}
			}

			if (mTerm instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) mTerm;
				final String connective = appTerm.getFunction().getName();
				final Term[] params = appTerm.getParameters();

				if (connective == "ite" || connective == "and" || connective == "or" || connective == "=>") {
					mSimplifiedParams = new Term[params.length];
					walkParam(simplifier);
					return;
				}
			}
			/* we could not simplify this term */
			simplifier.setResult(mNegated, mTerm);
			if (mContext != null) {
				simplifier.popContext();
			}
		}

		private void walkParam(final SimplifyDDA simplifier) {
			final ApplicationTerm appTerm = (ApplicationTerm) mTerm;
			final String connective = appTerm.getFunction().getName();
			final Term[] params = appTerm.getParameters();

			if (mParamCtr > 0) {
				mSimplifiedParams[mParamCtr - 1] = simplifier.popResult();
			}

			if (connective == "ite") {
				switch (mParamCtr++) {
				case 0:
					simplifier.enqueueWalker(this);
					simplifier.enqueueWalker(new Simplifier(false, params[0]));
					break;
				case 1:
					if (mSimplifiedParams[0] != simplifier.mFalse) {
						simplifier.enqueueWalker(this);
						simplifier.pushContext(mSimplifiedParams[0]);
						simplifier.enqueueWalker(new Simplifier(mNegated, params[1]));
						break;
					}
					mSimplifiedParams[mParamCtr - 1] = simplifier.mFalse;
					mParamCtr++;
					/* fall through */
				case 2:
					if (mSimplifiedParams[0] != simplifier.mFalse) {
						simplifier.popContext();
					}
					if (mSimplifiedParams[0] != simplifier.mTrue) {
						simplifier.enqueueWalker(this);
						simplifier.pushContext(Util.not(simplifier.mScript, mSimplifiedParams[0]));
						simplifier.enqueueWalker(new Simplifier(mNegated, params[2]));
						break;
					}
					mSimplifiedParams[mParamCtr - 1] = simplifier.mFalse;
					mParamCtr++;
					/* fall through */
				case 3: // NOCHECKSTYLE
					if (mSimplifiedParams[0] != simplifier.mTrue) {
						simplifier.popContext();
					}
					final Term result = Util.ite(simplifier.mScript, mSimplifiedParams[0], mSimplifiedParams[1],
							mSimplifiedParams[2]);
					simplifier.setResult(false, result);
					if (mContext != null) {
						simplifier.popContext();
					}
					break;
				default:
					throw new InternalError("BUG!");
				}
			} else {
				assert (connective == "and" || connective == "or" || connective == "=>");
				if (mParamCtr == params.length) {
					simplifier.popContext();
					final ArrayList<Term> newparams = new ArrayList<>();
					Term result = null;
					for (int i = 0; i < mSimplifiedParams.length; i++) {
						final Term param = mSimplifiedParams[i];
						if (param == simplifier.mTrue) {
							if (connective == "and" || (connective == "=>" && i < mSimplifiedParams.length - 1)) {
								continue;
							}
							if (connective == "or" || (connective == "=>" && i == mSimplifiedParams.length - 1)) {
								result = simplifier.mTrue;
								break;
							}
						} else if (param == simplifier.mFalse) {
							if (connective == "or") {
								continue;
							}
							if (connective == "and") {
								result = simplifier.mFalse;
								break;
							}
							if (connective == "=>" && i < mSimplifiedParams.length - 1) {
								result = simplifier.mTrue;
								break;
							}
						}
						newparams.add(param);
					}
					if (result == null) {
						if (newparams.isEmpty()) {
							result = connective == "and" ? simplifier.mTrue : simplifier.mFalse;
						} else if (newparams.size() == 1) {
							result = newparams.get(0);
						} else {
							final Term[] p = newparams.toArray(new Term[newparams.size()]);
							result = simplifier.mScript.term(connective, p);
						}
					}
					simplifier.setResult(mNegated, result);
					if (mContext != null) {
						simplifier.popContext();
					}
					return;
				}
				if (mParamCtr == 0) {
					simplifier.pushContext();
					for (int i = params.length - 1; i >= 1; i--) {
						final Term sibling = simplifier.negateSibling(params[i], connective, i, params.length);
						simplifier.pushContext(sibling);
					}
				} else {
					simplifier.popContext();
					for (int i = 0; i < mParamCtr; i++) {
						final Term sibling =
								simplifier.negateSibling(mSimplifiedParams[i], connective, i, params.length);
						final LBool sat = simplifier.mScript.assertTerm(sibling);
						if (sat == LBool.UNSAT) {
							simplifier.mInconsistencyOfContextDetected = true;
							break;
						}
					}
				}
				simplifier.enqueueWalker(this);
				simplifier.enqueueWalker(new Simplifier(false, params[mParamCtr]));
				mParamCtr++;
			}
		}

		@Override
		public String toString() {
			return "Simplifier[" + mTerm + ", param: " + mParamCtr + "]";
		}
	}

	/**
	 * Creates a simplifier. This will simplify repeatedly until a fixpoint is reached.
	 *
	 * @param script
	 *            A Script object that will be used to check for equivalent formulas.
	 */
	public SimplifyDDA(final Script script) {
		this(script, true);
	}

	/**
	 * Creates a simplifier.
	 *
	 * @param script
	 *            A Script object that will be used to check for equivalent formulas.
	 * @param simplifyRepeatedly
	 *            true if the simplifier should run until a fixpoint is reached.
	 */
	public SimplifyDDA(final Script script, final boolean simplifyRepeatedly) {
		mScript = script;
		mTrue = mScript.term("true");
		mFalse = mScript.term("false");
		mSimplifyRepeatedly = simplifyRepeatedly;
	}

	/**
	 * Redundancy is a property of a subterm B with respect to its term A. The subterm B is called:
	 * <ul>
	 * <li>NON_RELAXING if term A is equivalent to the term, where B is replaced by false.
	 * <li>NON_CONSTRAINING if term A is equivalent to the term, where B is replaced by true.
	 * <li>NOT_REDUNDANT B is neither NON_REAXING nor NON_CONSTRAINING with respect to A.
	 * </ul>
	 */
	public enum Redundancy {
		NON_RELAXING, NON_CONSTRAINING, NOT_REDUNDANT
	}

	/**
	 * Checks if termA is equivalent to termB. Returns unsat if the terms are equivalent, sat if they are not and
	 * unknown if it is not possible to determine.
	 */
	public LBool checkEquivalence(final Term termA, final Term termB) {
		final Term equivalentTestTerm = mScript.term("=", termA, termB);
		String checktype = null;
		try {
			checktype = (String) mScript.getOption(":check-type");
			mScript.setOption(":check-type", "FULL");
		} catch (final UnsupportedOperationException ignored) {
			// Solver is not SMTInterpol
		}
		final LBool areTermsEquivalent = Util.checkSat(mScript, Util.not(mScript, equivalentTestTerm));
		if (checktype != null) {
			mScript.setOption(":check-type", checktype);
		}
		return areTermsEquivalent;
	}

	/**
	 * Checks if term is redundant, with respect to the critical constraint on the assertion stack.
	 *
	 * @return NON_CONSTRAINING if term is equivalent to true, NON_RELAXING if term is equivalent to true, NOT_REDUNDANT
	 *         if term is not redundant.
	 */
	protected Redundancy getRedundancy(final Term term) {
		if (mInconsistencyOfContextDetected) {
			// context already inconsistent, hence term is
			// NON_CONSTRAINING and NON_RELAXING
			return Redundancy.NON_CONSTRAINING;
		}
		final LBool isTermConstraining = Util.checkSat(mScript, Util.not(mScript, term));
		if (isTermConstraining == LBool.UNSAT) {
			return Redundancy.NON_CONSTRAINING;
		}

		final LBool isTermRelaxing = Util.checkSat(mScript, term);
		if (isTermRelaxing == LBool.UNSAT) {
			return Redundancy.NON_RELAXING;
		}

		return Redundancy.NOT_REDUNDANT;
	}

	private static Term termVariable2constant(final Script script, final TermVariable tv) {
		final String name = tv.getName() + "_const_" + tv.hashCode();
		final Sort[] paramSorts = {};
		final Sort resultSort = tv.getSort();
		script.declareFun(name, paramSorts, resultSort);
		final Term result = script.term(name);
		return result;
	}

	public Term simplifyOnce(final Term term) {
		mInconsistencyOfContextDetected = false;
		mTermInfos = new HashMap<>();

		run(new TermCounter(term));
		run(new ContextCollector(false, term, new ArrayDeque<Term>()));
		run(new PrepareSimplifier(false, term));
		run(new Simplifier(false, term));
		final Term output = popResult();

		mTermInfos = null;
		return output;
	}

	/**
	 * Return a Term which is equivalent to term but whose number of leaves is less than or equal to the number of
	 * leaves in term.
	 *
	 * @return term if each subterm of term is neither NON_CONSTRAINING nor NON_RELAXING. Otherwise return a copy of
	 *         term, where each NON_CONSTRAINING subterm is replaced by true and each NON_RELAXING subterm is replaced
	 *         by false
	 * @param mTerm
	 *            whose Sort is Boolean
	 */
	public Term getSimplifiedTerm(final Term inputTerm) throws SMTLIBException {
		// mLogger.debug("Simplifying " + term);
		/* We can only simplify boolean terms. */
		if (!"Bool".equals(inputTerm.getSort().getName())) {
			return inputTerm;
		}
		int lvl = 0;// Java requires initialization
		assert (lvl = PushPopChecker.currentLevel(mScript)) >= -1;
		Term term = inputTerm;
		mScript.echo(new QuotedObject("Begin Simplifier"));
		mScript.push(1);
		final TermVariable[] vars = term.getFreeVars();
		final Term[] values = new Term[vars.length];
		for (int i = 0; i < vars.length; i++) {
			values[i] = termVariable2constant(mScript, vars[i]);
		}
		term = mScript.let(vars, values, term);

		term = new FormulaUnLet().unlet(term);

		Term output = simplifyOnce(term);
		if (mSimplifyRepeatedly) {
			while (output != term) {
				term = output;
				output = simplifyOnce(term);
			}
		} else {
			term = output;
		}

		term = new TermTransformer() {
			@Override
			public void convert(Term innerTerm) {
				for (int i = 0; i < vars.length; i++) {
					if (innerTerm == values[i]) {
						innerTerm = vars[i];
					}
				}
				super.convert(innerTerm);
			}
		}.transform(term);// NOCHECKSTYLE
		mScript.pop(1);
		assert (checkEquivalence(inputTerm, term) != LBool.SAT) : "Simplification unsound?";
		mScript.echo(new QuotedObject("End Simplifier"));
		assert PushPopChecker.atLevel(mScript, lvl);
		return term;
	}

	/**
	 * Returns the contribution of a sibling to the critical constraint. This is either the sibling itself or its
	 * negation. The result is the negated sibling iff
	 * <ul>
	 * <li>the connective is "or"
	 * <li>the connective is "=>" and i==n-1
	 * </ul>
	 *
	 * @param i
	 *            Index of this sibling. E.g., sibling B has index 1 in the term (and A B C)
	 * @param n
	 *            Number of all siblings. E.g., the term (and A B C) has three siblings.
	 */
	private Term negateSibling(final Term sibling, final String connective, final int i, final int n) {
		final boolean negate = (connective == "or" || connective == "=>" && i == n - 1);
		if (negate) {
			return Util.not(mScript, sibling);
		}
		return sibling;
	}

	void pushContext(final Term... context) {
		mScript.push(1);
		for (final Term t : context) {
			final LBool sat = mScript.assertTerm(t);
			if (sat == LBool.UNSAT) {
				mInconsistencyOfContextDetected = true;
				return;
			}
		}
	}

	void popContext() {
		mInconsistencyOfContextDetected = false;
		mScript.pop(1);
	}

	void setResult(final boolean negated, Term term) {
		if (negated) {
			term = Util.not(mScript, term);
		}
		assert (mResult == null);
		mResult = term;
	}

	Term popResult() {
		final Term result = mResult;
		mResult = null;
		return result;
	}
}
