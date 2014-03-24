/*
 * Copyright (C) 2012 University of Freiburg
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

import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;

/**
 * Helper class that can be used by other term transformers to build partial
 * formulas in our internal not-or-tree format.
 * @author Juergen Christ
 */
public class Utils {
	
	private final IProofTracker mTracker;
	
	private final TermCompiler mCompiler;
	
	public Utils(IProofTracker tracker, TermCompiler compiler) {
		mTracker = tracker;
		mCompiler = compiler;
	}
	/**
	 * Optimize nots.  Transforms (not true) to false, (not false) to true, and
	 * remove double negation.
	 * @param arg Term to negate.
	 * @return Term equivalent to the negation of the input.
	 */
	public Term createNot(Term arg) {
		Theory theory = arg.getTheory();
		if (arg == theory.mFalse) {
			mTracker.negation(arg, theory.mTrue, ProofConstants.RW_NOT_SIMP);
			return theory.mTrue;
		}
		if (arg == theory.mTrue) {
			mTracker.negation(arg, theory.mFalse, ProofConstants.RW_NOT_SIMP);
			return theory.mFalse;
		}
		if ((arg instanceof ApplicationTerm)
			&& ((ApplicationTerm) arg).getFunction().getName().equals("not")) {
			Term res = ((ApplicationTerm) arg).getParameters()[0];
			mTracker.negation(arg, res, ProofConstants.RW_NOT_SIMP);
			return res;
		}
		return theory.term("not", arg);
	}
	
	public static Term createNotUntracked(Term arg) {
		Theory theory = arg.getTheory();
		if (arg == theory.mFalse)
			return theory.mTrue;
		if (arg == theory.mTrue)
			return theory.mFalse;
		if ((arg instanceof ApplicationTerm)
			&& ((ApplicationTerm) arg).getFunction().getName().equals("not"))
			return ((ApplicationTerm) arg).getParameters()[0];
		return theory.term("not", arg);
	}
	/**
	 * Optimize ors.  If true is found in the disjuncts, it is returned.
	 * Otherwise, we remove false, or disjuncts that occur more than once.  The
	 * result might still be an n-ary or.
	 * @param args The disjuncts.
	 * @return Term equivalent to the disjunction of the disjuncts.
	 */
	public Term createOr(Term... args) {
		LinkedHashSet<Term> ctx = new LinkedHashSet<Term>();
		Theory theory = args[0].getTheory();
		Term trueTerm = theory.mTrue;
		Term falseTerm = theory.mFalse;
		for (Term t : args) {
			if (t == trueTerm) {
				mTracker.or(args, t, ProofConstants.RW_OR_TAUT);
				return t;
			}
			if (t != falseTerm) {
				if (ctx.contains(createNotUntracked(t))) {
					mTracker.or(args, trueTerm, ProofConstants.RW_OR_TAUT);
					return trueTerm;
				}
				ctx.add(t);
			}
		}
		// Handle disjunctions of false
		if (ctx.isEmpty()) {
			mTracker.or(args, theory.mFalse, ProofConstants.RW_OR_SIMP);
			return theory.mFalse;
		}
		// Handle simplifications to unary or
		if (ctx.size() == 1) {
			Term res = ctx.iterator().next();
			mTracker.or(args, res, ProofConstants.RW_OR_SIMP);
			return res;
		}
		if (ctx.size() == args.length)
			return theory.term(theory.mOr, args);
		Term res = theory.term(theory.mOr, ctx.toArray(new Term[ctx.size()]));
		mTracker.or(args, res, ProofConstants.RW_OR_SIMP);
		return res;
	}
	public Term createLeq0(SMTAffineTerm arg) {
		if (arg.isConstant()) {
			Theory t = arg.getTheory();
			if (arg.getConstant().compareTo(Rational.ZERO) > 0) {
				mTracker.leqSimp(arg, t.mFalse, ProofConstants.RW_LEQ_FALSE);
				return t.mFalse;
			} else {
				mTracker.leqSimp(arg, t.mTrue, ProofConstants.RW_LEQ_TRUE);
				return t.mTrue;
			}
		}
		return arg.getTheory().term("<=", arg.normalize(mCompiler),
				SMTAffineTerm.create(Rational.ZERO, arg.getSort()));
	}
	/**
	 * Simplify ite terms.  This might destroy the ite if it is Boolean with
	 * at least one constant leaf, or if the leaves equal. 
	 * @param cond			Condition of the ite.
	 * @param trueBranch	What should be true if the condition holds.
	 * @param falseBranch	What should be true if the condition does not hold.
	 * @return Term equivalent to (ite cond trueBranch falseBranch).
	 */
	public Term createIte(Term cond, Term trueBranch, Term falseBranch) {
		Theory theory = cond.getTheory();
		if (cond == theory.mTrue) {
			mTracker.ite(cond, trueBranch, falseBranch, trueBranch,
					ProofConstants.RW_ITE_TRUE);
			return trueBranch;
		}
		if (cond == theory.mFalse) {
			mTracker.ite(cond, trueBranch, falseBranch, falseBranch,
					ProofConstants.RW_ITE_FALSE);
			return falseBranch;
		}
		if (trueBranch == falseBranch) {
			mTracker.ite(cond, trueBranch, falseBranch, trueBranch,
					ProofConstants.RW_ITE_SAME);
			return trueBranch;
		}
		if (trueBranch == theory.mTrue && falseBranch == theory.mFalse) {
			mTracker.ite(cond, trueBranch, falseBranch, cond,
					ProofConstants.RW_ITE_BOOL_1);
			return cond;
		}
		if (trueBranch == theory.mFalse && falseBranch == theory.mTrue) {
			mTracker.ite(cond, trueBranch, falseBranch, null,
					ProofConstants.RW_ITE_BOOL_2);
			return createNot(cond);
		}
		if (trueBranch == theory.mTrue) {
			// No need for createOr since we are already sure that we cannot
			// simplify further
			Term res = theory.term("or", cond, falseBranch);
			mTracker.ite(cond, trueBranch, falseBranch, res,
					ProofConstants.RW_ITE_BOOL_3);
			return createOr(cond, falseBranch);
		}
		if (trueBranch == theory.mFalse) {
			// /\ !cond falseBranch => !(\/ cond !falseBranch)
			mTracker.ite(cond, trueBranch, falseBranch, null,
					ProofConstants.RW_ITE_BOOL_4);
			return createNot(createOr(cond, createNot(falseBranch)));
		}
		if (falseBranch == theory.mTrue) {
			// => cond trueBranch => \/ !cond trueBranch
			mTracker.ite(cond, trueBranch, falseBranch, null,
					ProofConstants.RW_ITE_BOOL_5);
			return createOr(createNot(cond), trueBranch);
		}
		if (falseBranch == theory.mFalse) {
			// /\ cond trueBranch => !(\/ !cond !trueBranch)
			mTracker.ite(cond, trueBranch, falseBranch, null,
					ProofConstants.RW_ITE_BOOL_6);
			return createNot(createOr(createNot(cond), createNot(trueBranch)));
		}
		return theory.term("ite", cond, trueBranch, falseBranch);
	}
	/**
	 * Optimize equalities.  This function creates binary equalities out of
	 * n-ary equalities.  First, we optimize the arguments of the equality by
	 * removing double entries, multiple constants, and transforms Boolean
	 * equalities to true, false, and, or or in case of constant parameters.
	 * @param args The arguments of the equality.
	 * @return A term equivalent to the equality of all input terms.
	 */
	public Term createEq(Term... args) {
		LinkedHashSet<Term> tmp = new LinkedHashSet<Term>();
		Theory theory = args[0].getTheory();
		if (args[0].getSort().isNumericSort()) {
			Rational lastConst = null;
			for (Term t : args) {
				if (t instanceof ConstantTerm || t instanceof SMTAffineTerm) {
					SMTAffineTerm at = SMTAffineTerm.create(t);
					if (at.isConstant()) {
						if (lastConst == null) {
							lastConst = at.getConstant();
						} else if (!lastConst.equals(at.getConstant())) {
							mTracker.equality(args, theory.mFalse,
									ProofConstants.RW_CONST_DIFF);
							return theory.mFalse;
						}
					}
				}
				tmp.add(t);
			}
		} else if (args[0].getSort() == theory.getBooleanSort()) {
			// Idea: if we find false:
			//       - If we additionally find true: return false
			//       - Otherwise we have to negate all other occurrences
			//       if we only find true:
			//       - conjoin all elements
			boolean foundTrue = false;
			boolean foundFalse = false;
			for (Term t : args) {
				if (t == theory.mTrue) {
					foundTrue = true;
					if (foundFalse) {
						mTracker.equality(args, theory.mFalse,
								ProofConstants.RW_TRUE_NOT_FALSE);
						return theory.mFalse;
					}
				} else if (t == theory.mFalse) {
					foundFalse = true;
					if (foundTrue) {
						mTracker.equality(args, theory.mFalse,
								ProofConstants.RW_TRUE_NOT_FALSE);
						return theory.mFalse;
					}
				} else
					tmp.add(t);
			}
			if (foundTrue) {
				// take care of (= true true ... true)
				if (tmp.isEmpty()) {
					mTracker.equality(args, theory.mTrue,
							ProofConstants.RW_EQ_SAME);
					return theory.mTrue;
				}
				Term[] tmpArgs = tmp.toArray(new Term[tmp.size()]);
				mTracker.equality(args, tmpArgs, ProofConstants.RW_EQ_TRUE);
				if (tmpArgs.length == 1)
					return tmpArgs[0];
				return createAndInplace(tmpArgs);
			}
			if (foundFalse) {
				if (tmp.isEmpty()) {
					mTracker.equality(args, theory.mTrue,
							ProofConstants.RW_EQ_SAME);
					return theory.mTrue;
				}
				Term[] tmpArgs = tmp.toArray(new Term[tmp.size()]);
				mTracker.equality(args, tmpArgs, ProofConstants.RW_EQ_FALSE);
				if (tmpArgs.length == 1)
					return createNot(tmpArgs[0]);
				// take care of (= false false ... false)
				return createNot(createOr(tmpArgs));
			}
		} else {
			for (Term t : args)
				tmp.add(t);
		}
		// We had (= a ... a)
		if (tmp.size() == 1) {
			mTracker.equality(args, theory.mTrue, ProofConstants.RW_EQ_SAME);
			return theory.mTrue;
		}
		// Make binary
		Term[] tmpArray = tmp.size() == args.length
		        ? args : tmp.toArray(new Term[tmp.size()]);
		if (args != tmpArray)
			mTracker.equality(args, tmpArray, ProofConstants.RW_EQ_SIMP);
		if (tmpArray.length == 2)
			return makeBinaryEq(tmpArray);
		Term[] conj = new Term[tmpArray.length - 1];
		for (int i = 0; i < conj.length; ++i)
			conj[i] = theory.term("not",
					makeBinaryEq(tmpArray[i], tmpArray[i + 1]));
		Term res = theory.term("not", theory.term("or", conj));
		mTracker.equality(tmpArray, res, ProofConstants.RW_EQ_BINARY);
		return res;
	}
	
	private Term storeRewrite(ApplicationTerm store, boolean arrayFirst) {
		assert isStore(store) : "Not a store in storeRewrite";
		Theory t = store.getTheory();
		// have (store a i v)
		// produce (select a i) = v
		Term[] args = store.getParameters();
		Term result = t.term("=", t.term("select", args[0], args[1]), args[2]);
		mTracker.storeRewrite(store, result, arrayFirst);
		return result;
	}
	private boolean isStore(Term t) {
		if (t instanceof ApplicationTerm) {
			FunctionSymbol fs = ((ApplicationTerm) t).getFunction();
			return fs.isIntern() && fs.getName().equals("store");
		}
		return false;
	}
	/**
	 * Make a binary equality.  Note that the precondition of this function
	 * requires the caller to ensure that the argument array contains only two
	 * terms.  
	 * 
	 * This function is used to detect store-idempotencies.
	 * @return A binary equality.
	 */
	private Term makeBinaryEq(Term... args) {
		assert args.length == 2 : "Non-binary equality in makeBinaryEq";
		if (args[0].getSort().isArraySort()) {
			// Check store-rewrite
			if (isStore(args[0])) {
				Term array = ((ApplicationTerm) args[0]).getParameters()[0];
				if (args[1] == array)
					return storeRewrite((ApplicationTerm) args[0], false);
			}
			if (isStore(args[1])) {
				Term array = ((ApplicationTerm) args[1]).getParameters()[0];
				if (args[0] == array)
					return storeRewrite((ApplicationTerm) args[1], true);
			}
		}
		return args[0].getTheory().term("=", args);
	}
	/**
	 * Simplify distincts.  At the moment, we remove distinct constructs and
	 * replace them by negated equalities.  We optimize Boolean distincts, and
	 * transform non-Boolean distincts to false, if we have multiple times the
	 * same term.
	 * @param args Terms that should be distinct.
	 * @return A term equivalent to the arguments applied to the distinct
	 * 			function.
	 */
	public Term createDistinct(Term... args) {
		Theory theory = args[0].getTheory();
		if (args[0].getSort() == theory.getBooleanSort()) {
			if (args.length > 2) {
				mTracker.distinct(args, theory.mFalse,
						ProofConstants.RW_DISTINCT_BOOL);
				return theory.mFalse;
			}
			Term t0 = args[0];
			Term t1 = args[1];
			if (t0 == t1) {
				mTracker.distinct(args, theory.mFalse,
						ProofConstants.RW_DISTINCT_SAME);
				return theory.mFalse;
			}
			if (t0 == createNotUntracked(t1)) {
				mTracker.distinct(args, theory.mTrue,
						ProofConstants.RW_DISTINCT_NEG);
				return theory.mTrue;
			}
			if (t0 == theory.mTrue) {
				mTracker.distinct(args, null, ProofConstants.RW_DISTINCT_TRUE);
				return createNot(t1);
			}
			if (t0 == theory.mFalse) {
				mTracker.distinct(args, t1, ProofConstants.RW_DISTINCT_FALSE);
				return t1;
			}
			if (t1 == theory.mTrue) {
				mTracker.distinct(args, null, ProofConstants.RW_DISTINCT_TRUE);
				return createNot(t0);
			}
			if (t1 == theory.mFalse) {
				mTracker.distinct(args, t0, ProofConstants.RW_DISTINCT_FALSE);
				return t0;
			}
			// Heuristics: Try to find an already negated term
			if (isNegation(t0)) {
				mTracker.distinctBoolEq(t0, t1, true);
				return theory.term("=", createNot(t0), t1);
			}
			mTracker.distinctBoolEq(t0, t1, false);
			return theory.term("=", t0, createNot(t1));
		}
		LinkedHashSet<Term> tmp = new LinkedHashSet<Term>();
		for (Term t : args)
			if (!tmp.add(t)) {
				// We had (distinct a b a)
				mTracker.distinct(args, theory.mFalse,
						ProofConstants.RW_DISTINCT_SAME);
				return theory.mFalse;
			}
		tmp = null;
		if (args.length == 2) {
			Term res = theory.term("not", theory.term("=", args));
			mTracker.distinct(args, res, ProofConstants.RW_DISTINCT_BINARY);
			return res;
		}
		// We need n * (n - 1) / 2 conjuncts
		Term[] nconjs = new Term[args.length * (args.length - 1) / 2];
		int pos = 0;
		for (int i = 0; i < args.length - 1; ++i)
			for (int j = i + 1; j < args.length; ++j)
				nconjs[pos++] = theory.term("=", args[i], args[j]);
		Term res = theory.term("not", theory.term("or", nconjs));
		mTracker.distinct(args, res, ProofConstants.RW_DISTINCT_BINARY);
		return res;
//		return theory.term("distinct", args);
	}
	public static boolean isNegation(Term t) {
		if (t instanceof ApplicationTerm)
			return ((ApplicationTerm) t).getFunction() == t.getTheory().mNot;
		return false;
	}
	public Term createAndInplace(Term... args) {
		assert (args.length > 1) : "Invalid and in simplification";
		mTracker.removeConnective(args, null, ProofConstants.RW_AND_TO_OR);
		for (int i = 0; i < args.length; ++i)
			args[i] = createNot(args[i]);
		return createNot(createOr(args));
	}
	public Term createAnd(Term... args) {
		args = args.clone();
		return createAndInplace(args);
	}
}
