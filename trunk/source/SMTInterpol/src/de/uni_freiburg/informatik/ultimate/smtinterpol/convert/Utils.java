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

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
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


	public Utils(final IProofTracker tracker) {
		mTracker = tracker;
	}

	/**
	 * Optimize nots.  Transforms (not true) to false, (not false) to true, and
	 * remove double negation.
	 * @param arg Term to negate.
	 * @return Term equivalent to the negation of the input.
	 */
	public Term convertNot(final Term input) {
		final ApplicationTerm notTerm = (ApplicationTerm) mTracker.getProvedTerm(input);
		assert notTerm.getFunction().getName() == "not";
		final Theory theory = notTerm.getTheory();
		final Term arg = notTerm.getParameters()[0];
		if (arg == theory.mFalse) {
			final Term rewrite = mTracker.buildRewrite(notTerm, theory.mTrue, ProofConstants.RW_NOT_SIMP);
			return mTracker.transitivity(input, rewrite);
		}
		if (arg == theory.mTrue) {
			final Term rewrite = mTracker.buildRewrite(notTerm, theory.mFalse, ProofConstants.RW_NOT_SIMP);
			return mTracker.transitivity(input, rewrite);
		}
		if ((arg instanceof ApplicationTerm)
			&& ((ApplicationTerm) arg).getFunction().getName().equals("not")) {
			final Term res = ((ApplicationTerm) arg).getParameters()[0];
			final Term rewrite = mTracker.buildRewrite(notTerm, res, ProofConstants.RW_NOT_SIMP);
			return mTracker.transitivity(input, rewrite);
		}
		return input;
	}

	/**
	 * Optimize ors.  If true is found in the disjuncts, it is returned.
	 * Otherwise, we remove false, or disjuncts that occur more than once.  The
	 * result might still be an n-ary or.
	 * @param args The disjuncts.
	 * @return Term equivalent to the disjunction of the disjuncts.
	 */
	public Term convertOr(final Term input) {
		final ApplicationTerm orTerm = (ApplicationTerm) mTracker.getProvedTerm(input);
		assert orTerm.getFunction().getName() == "or";
		final Term[] args = orTerm.getParameters();
		final LinkedHashSet<Term> ctx = new LinkedHashSet<Term>();
		final Theory theory = args[0].getTheory();
		final Term trueTerm = theory.mTrue;
		final Term falseTerm = theory.mFalse;
		for (final Term t : args) {
			if (t == trueTerm) {
				return mTracker.transitivity(input,
						mTracker.buildRewrite(orTerm, trueTerm, ProofConstants.RW_OR_TAUT));
			}
			if (t != falseTerm) {
				if (ctx.contains(theory.not(t))) {
					return mTracker.transitivity(input,
							mTracker.buildRewrite(orTerm, trueTerm, ProofConstants.RW_OR_TAUT));
				}
				ctx.add(t);
			}
		}
		// Handle disjunctions of false
		if (ctx.isEmpty()) {
			return mTracker.transitivity(input,
					mTracker.buildRewrite(orTerm, falseTerm, ProofConstants.RW_OR_SIMP));
		}
		// Handle simplifications to unary or
		if (ctx.size() == 1) {
			final Term res = ctx.iterator().next();
			return mTracker.transitivity(input,
					mTracker.buildRewrite(orTerm, res, ProofConstants.RW_OR_SIMP));
		}
		if (ctx.size() == args.length) {
			return input;
		}
		final Term res = theory.term(theory.mOr, ctx.toArray(new Term[ctx.size()]));
		return mTracker.transitivity(input,
				mTracker.buildRewrite(orTerm, res, ProofConstants.RW_OR_SIMP));
	}

	public Term convertLeq0(final Term input) {
		final ApplicationTerm leq0Term = (ApplicationTerm) mTracker.getProvedTerm(input);
		assert leq0Term.getFunction().getName() == "<=";
		assert leq0Term.getParameters()[1] == Rational.ZERO.toTerm(leq0Term.getParameters()[0].getSort());
		final Term arg = leq0Term.getParameters()[0];
		if (arg instanceof ConstantTerm) {
			final Rational value = (Rational) ((ConstantTerm) arg).getValue();
			final Theory t = arg.getTheory();
			if (value.compareTo(Rational.ZERO) > 0) {
				return mTracker.transitivity(input,
						mTracker.buildRewrite(leq0Term, t.mFalse, ProofConstants.RW_LEQ_FALSE));
			} else {
				return mTracker.transitivity(input,
						mTracker.buildRewrite(leq0Term, t.mTrue, ProofConstants.RW_LEQ_TRUE));
			}
		}
		return input;
	}

	/**
	 * Simplify ite terms.  This might destroy the ite if it is Boolean with
	 * at least one constant leaf, or if the leaves equal.
	 * @param cond			Condition of the ite.
	 * @param trueBranch	What should be true if the condition holds.
	 * @param falseBranch	What should be true if the condition does not hold.
	 * @return Term equivalent to (ite cond trueBranch falseBranch).
	 */
	public Term convertIte(final Term input) {
		final ApplicationTerm iteTerm = (ApplicationTerm) mTracker.getProvedTerm(input);
		assert iteTerm.getFunction().getName() == "ite";
		final Term cond = iteTerm.getParameters()[0];
		final Term trueBranch = iteTerm.getParameters()[1];
		final Term falseBranch = iteTerm.getParameters()[2];
		final Theory theory = cond.getTheory();
		if (cond == theory.mTrue) {
			return mTracker.transitivity(input,
					mTracker.buildRewrite(iteTerm, trueBranch, ProofConstants.RW_ITE_TRUE));
		}
		if (cond == theory.mFalse) {
			return mTracker.transitivity(input,
					mTracker.buildRewrite(iteTerm, falseBranch, ProofConstants.RW_ITE_FALSE));
		}
		if (trueBranch == falseBranch) {
			return mTracker.transitivity(input,
					mTracker.buildRewrite(iteTerm, trueBranch, ProofConstants.RW_ITE_SAME));
		}
		if (trueBranch == theory.mTrue && falseBranch == theory.mFalse) {
			return mTracker.transitivity(input,
					mTracker.buildRewrite(iteTerm, cond, ProofConstants.RW_ITE_BOOL_1));
		}
		if (trueBranch == theory.mFalse && falseBranch == theory.mTrue) {
			final Term result = mTracker.transitivity(input,
					mTracker.buildRewrite(iteTerm, theory.term("not", cond), ProofConstants.RW_ITE_BOOL_2));
			return convertNot(result);
		}
		if (trueBranch == theory.mTrue) {
			final Term result = mTracker.transitivity(input,
					mTracker.buildRewrite(iteTerm, theory.term("or", cond, falseBranch), ProofConstants.RW_ITE_BOOL_3));
			return convertOr(result);
		}
		if (trueBranch == theory.mFalse) {
			// /\ !cond falseBranch => !(\/ cond !falseBranch)
			final Term rhs = theory.term("not", theory.term("or", cond, theory.term("not", falseBranch)));
			final Term result = mTracker.transitivity(input,
					mTracker.buildRewrite(iteTerm, rhs, ProofConstants.RW_ITE_BOOL_4));
			return convertNotOrNot(result);
		}
		if (falseBranch == theory.mTrue) {
			// => cond trueBranch => \/ !cond trueBranch
			final Term rhs = theory.term("or", theory.term("not", cond), trueBranch);
			final Term result = mTracker.transitivity(input,
					mTracker.buildRewrite(iteTerm, rhs, ProofConstants.RW_ITE_BOOL_5));
			return convertOrNot(result);
		}
		if (falseBranch == theory.mFalse) {
			// /\ cond trueBranch => !(\/ !cond !trueBranch)
			final Term rhs = theory.term("not", theory.term("or", theory.term("not", cond), theory.term("not", trueBranch)));
			final Term result = mTracker.transitivity(input,
					mTracker.buildRewrite(iteTerm, rhs, ProofConstants.RW_ITE_BOOL_6));
			return convertNotOrNot(result);
		}
		return input;
	}

	/**
	 * Make a binary equality.  Note that the precondition of this function
	 * requires the caller to ensure that the argument array contains only two
	 * terms.
	 *
	 * This function is used to detect store-idempotencies.
	 * @return A binary equality.
	 */
	public Term convertBinaryEq(final Term input) {
		final ApplicationTerm eqTerm = (ApplicationTerm) mTracker.getProvedTerm(input);
		assert eqTerm.getFunction().getName() == "=";
		final Term[] args = eqTerm.getParameters();
		assert args.length == 2 : "Non-binary equality in makeBinaryEq";
		if (args[0].getSort().isArraySort()) {
			// Check store-rewrite
			if (isStore(args[0])) {
				final ApplicationTerm store = (ApplicationTerm) args[0];
				if (args[1] == store.getParameters()[0]) {
					return convertStoreRewrite(input, store, false);
				}
			}
			if (isStore(args[1])) {
				final ApplicationTerm store = (ApplicationTerm) args[1];
				if (args[0] == store.getParameters()[0]) {
					return convertStoreRewrite(input, store, true);
				}
			}
		}
		return input;
	}

	/**
	 * Optimize equalities.  This function creates binary equalities out of
	 * n-ary equalities.  First, we optimize the arguments of the equality by
	 * removing double entries, multiple constants, and transforms Boolean
	 * equalities to true, false, and, or or in case of constant parameters.
	 * @param args The arguments of the equality.
	 * @return A term equivalent to the equality of all input terms.
	 */
	public Term convertEq(Term input) {
		ApplicationTerm eqTerm = (ApplicationTerm) mTracker.getProvedTerm(input);
		assert eqTerm.getFunction().getName() == "=";
		final Theory theory = input.getTheory();
		Term[] args = eqTerm.getParameters();
		final LinkedHashSet<Term> eqArgList = new LinkedHashSet<Term>();
		if (args[0].getSort().isNumericSort()) {
			Rational lastConst = null;
			for (final Term t : args) {
				if (t instanceof ConstantTerm) {
					final Rational value = (Rational) ((ConstantTerm) t).getValue();
					if (lastConst == null) {
						lastConst = value;
					} else if (!lastConst.equals(value)) {
						return mTracker.transitivity(input,
								mTracker.buildRewrite(eqTerm, theory.mFalse, ProofConstants.RW_CONST_DIFF));
					}
				}
				eqArgList.add(t);
			}
		} else if (args[0].getSort() == theory.getBooleanSort()) {
			// Idea: if we find false:
			//       - If we additionally find true: return false
			//       - Otherwise we have to negate all other occurrences
			//       if we only find true:
			//       - conjoin all elements
			boolean foundTrue = false;
			boolean foundFalse = false;
			for (final Term t : args) {
				if (t == theory.mTrue) {
					foundTrue = true;
				} else if (t == theory.mFalse) {
					foundFalse = true;
				} else {
					eqArgList.add(t);
				}
			}
			if (foundTrue && foundFalse) {
				return mTracker.transitivity(input,
						mTracker.buildRewrite(eqTerm, theory.mFalse, ProofConstants.RW_TRUE_NOT_FALSE));
			}
			if (foundTrue || foundFalse) {
				// take care of (= true ... true) or (= false ... false)
				if (eqArgList.isEmpty()) {
					return mTracker.transitivity(input,
							mTracker.buildRewrite(eqTerm, theory.mTrue, ProofConstants.RW_EQ_SAME));
				}

				final Annotation rule = foundTrue ? ProofConstants.RW_EQ_TRUE : ProofConstants.RW_EQ_FALSE;
				// create (not (or ...))
				final Term[] orArgs = eqArgList.toArray(new Term[eqArgList.size()]);
				Term rhs;
				if (orArgs.length == 1) {
					// (= true x) resp. (= false x) --> x resp. (not x)
					rhs = orArgs[0];
					if (foundFalse) {
						rhs = theory.term("not", rhs);
					}
					Term rewrite = mTracker.transitivity(input, mTracker.buildRewrite(eqTerm, rhs, rule));
					if (foundFalse) {
						rewrite = convertNot(rewrite);
					}
					return rewrite;
				} else {
					if (foundTrue) {
						// and all args ---> nested not
						for (int i = 0; i < orArgs.length; i++) {
							orArgs[i] = theory.term("not", orArgs[i]);
						}
					}
					rhs = theory.term("not", theory.term("or", orArgs));
					return convertNotOrNot(mTracker.transitivity(input,
							mTracker.buildRewrite(eqTerm, rhs, rule)));
				}
			}
		} else {
			for (final Term t : args) {
				eqArgList.add(t);
			}
		}
		// We had (= a ... a)
		if (eqArgList.size() == 1) {
			return mTracker.transitivity(input,
					mTracker.buildRewrite(eqTerm, theory.mTrue, ProofConstants.RW_EQ_SAME));
		}
		// Simplify first
		if (eqArgList.size() != args.length) {
			final Term[] newArgs = eqArgList.toArray(new Term[eqArgList.size()]);
			final ApplicationTerm rhs = theory.term("=", newArgs);
			input = mTracker.transitivity(input,
					mTracker.buildRewrite(eqTerm, rhs, ProofConstants.RW_EQ_SIMP));
			eqTerm = rhs;
			args = newArgs;
		}
		// Make binary
		if (args.length == 2) {
			return convertBinaryEq(input);
		}

		final Term[] conj = new Term[args.length - 1];
		for (int i = 0; i < conj.length; ++i) {
			conj[i] = theory.term("not", theory.term("=", args[i], args[i + 1]));
		}
		final Term res = theory.term("not", theory.term("or", conj));
		return mTracker.transitivity(input, mTracker.buildRewrite(eqTerm, res, ProofConstants.RW_EQ_BINARY));
	}

	private Term convertStoreRewrite(final Term input, final ApplicationTerm store, final boolean arrayFirst) {
		final Term eqTerm = mTracker.getProvedTerm(input);
		assert isStore(store) : "Not a store in storeRewrite";
		final Theory t = store.getTheory();
		// have (= a (store a i v))
		// produce (select a i) = v
		final Term[] args = store.getParameters();
		Term result = t.term("=", t.term("select", args[0], args[1]), args[2]);
		result = mTracker.buildRewrite(eqTerm, result, ProofConstants.RW_STORE_REWRITE);
		return result;
	}
	private boolean isStore(final Term t) {
		if (t instanceof ApplicationTerm) {
			final FunctionSymbol fs = ((ApplicationTerm) t).getFunction();
			return fs.isIntern() && fs.getName().equals("store");
		}
		return false;
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
	public Term convertDistinct(final Term input) {
		final ApplicationTerm distinctTerm = (ApplicationTerm) mTracker.getProvedTerm(input);
		assert distinctTerm.getFunction().getName() == "distinct";
		final Term[] args = distinctTerm.getParameters();
		final Theory theory = input.getTheory();
		if (args[0].getSort() == theory.getBooleanSort()) {
			if (args.length > 2) {
				return mTracker.transitivity(input,
						mTracker.buildRewrite(distinctTerm, theory.mFalse, ProofConstants.RW_DISTINCT_BOOL));
			}
			Term t0 = args[0];
			Term t1 = args[1];
			if (t0 == t1) {
				return mTracker.transitivity(input,
						mTracker.buildRewrite(distinctTerm, theory.mFalse, ProofConstants.RW_DISTINCT_SAME));
			}
			if (t0 == theory.not(t1)) {
				return mTracker.transitivity(input,
						mTracker.buildRewrite(distinctTerm, theory.mTrue, ProofConstants.RW_DISTINCT_NEG));
			}
			if (t0 == theory.mTrue) {
				final Term rhs = theory.term("not", t1);
				return convertNot(mTracker.transitivity(input,
						mTracker.buildRewrite(distinctTerm, rhs, ProofConstants.RW_DISTINCT_TRUE)));
			}
			if (t0 == theory.mFalse) {
				return mTracker.transitivity(input,
						mTracker.buildRewrite(distinctTerm, t1, ProofConstants.RW_DISTINCT_FALSE));
			}
			if (t1 == theory.mTrue) {
				final Term rhs = theory.term("not", t0);
				return convertNot(mTracker.transitivity(input,
						mTracker.buildRewrite(distinctTerm, rhs, ProofConstants.RW_DISTINCT_TRUE)));
			}
			if (t1 == theory.mFalse) {
				return mTracker.transitivity(input,
						mTracker.buildRewrite(distinctTerm, t0, ProofConstants.RW_DISTINCT_FALSE));
			}
			// Heuristics: Try to find an already negated term
			if (isNegation(t0)) {
				t0 = theory.term("not", t0);
			} else {
				t1 = theory.term("not", t1);
			}
			final Term rhs = theory.term("=", t0, t1);
			final Term rewrite = mTracker.transitivity(input,
					mTracker.buildRewrite(distinctTerm, rhs, ProofConstants.RW_DISTINCT_BOOL_EQ));
			return convertFuncNot(rewrite);
		}
		LinkedHashSet<Term> tmp = new LinkedHashSet<Term>();
		for (final Term t : args) {
			if (!tmp.add(t)) {
				// We had (distinct a b a)
				return mTracker.transitivity(input,
						mTracker.buildRewrite(distinctTerm, theory.mFalse, ProofConstants.RW_DISTINCT_SAME));
			}
		}
		tmp = null;
		if (args.length == 2) {
			final Term res = theory.term("not", theory.term("=", args));
			return mTracker.transitivity(input,
					mTracker.buildRewrite(distinctTerm, res, ProofConstants.RW_DISTINCT_BINARY));
		}
		// We need n * (n - 1) / 2 conjuncts
		final Term[] nconjs = new Term[args.length * (args.length - 1) / 2];
		int pos = 0;
		for (int i = 0; i < args.length - 1; ++i) {
			for (int j = i + 1; j < args.length; ++j) {
				nconjs[pos++] = theory.term("=", args[i], args[j]);
			}
		}
		final Term res = theory.term("not", theory.term("or", nconjs));
		return mTracker.transitivity(input,
				mTracker.buildRewrite(distinctTerm, res, ProofConstants.RW_DISTINCT_BINARY));
	}
	public static boolean isNegation(final Term t) {
		if (t instanceof ApplicationTerm) {
			return ((ApplicationTerm) t).getFunction() == t.getTheory().mNot;
		}
		return false;
	}

	/* Simplify a (f ..) term where the f term can contain double negation terms. */
	public Term convertFuncNot(final Term input) {
		final ApplicationTerm appTerm = (ApplicationTerm) mTracker.getProvedTerm(input);
		final Term[] args = appTerm.getParameters();
		final Term[] argRewrites = new Term[args.length];
		for (int i = 0; i < args.length; i++) {
			argRewrites[i] = mTracker.reflexivity(args[i]);
			if (args[i] instanceof ApplicationTerm
				&& ((ApplicationTerm) args[i]).getFunction().getName() == "not") {
				argRewrites[i] = convertNot(argRewrites[i]);
			}
		}
		return mTracker.congruence(input, argRewrites);
	}

	/* Simplify a (or ..) term where the or term can contain double negation terms. */
	public Term convertOrNot(final Term input) {
		return convertOr(convertFuncNot(input));
	}

	/* Simplify a (not (or ..)) term where the or term can contain double negation terms. */
	public Term convertNotOrNot(final Term input) {
		final ApplicationTerm notTerm = (ApplicationTerm) mTracker.getProvedTerm(input);
		assert notTerm.getFunction().getName() == "not";
		final ApplicationTerm orTerm = (ApplicationTerm) notTerm.getParameters()[0];
		final Term orRewrite = convertOrNot(mTracker.reflexivity(orTerm));
		return convertNot(mTracker.congruence(input, new Term[] { orRewrite }));
	}

	public Term convertAnd(final Term input) {
		final ApplicationTerm andTerm = (ApplicationTerm) mTracker.getProvedTerm(input);
		assert andTerm.getFunction().getName() == "and";
		final Theory theory = input.getTheory();
		final Term[] args = andTerm.getParameters();
		final Term[] negArgs = new Term[args.length];
		for (int i = 0; i < args.length; i++) {
			negArgs[i] = theory.term("not", args[i]);
		}
		final Term notOrTerm = theory.term("not", theory.term("or", negArgs));
		final Term andRewrite = mTracker.buildRewrite(andTerm, notOrTerm, ProofConstants.RW_AND_TO_OR);
		return convertNotOrNot(mTracker.transitivity(input, andRewrite));
	}

	public Term convertXor(final Term input) {
		final ApplicationTerm xorTerm = (ApplicationTerm) mTracker.getProvedTerm(input);
		final Theory theory = input.getTheory();
		assert xorTerm.getFunction().getName() == "xor";
		final Term rhs = theory.term("distinct", xorTerm.getParameters());
		final Term xorRewrite = mTracker.buildRewrite(xorTerm, rhs, ProofConstants.RW_XOR_TO_DISTINCT);
		return convertDistinct(mTracker.transitivity(input, xorRewrite));
	}

	public Term convertImplies(final Term input) {
		final ApplicationTerm impliesTerm = (ApplicationTerm) mTracker.getProvedTerm(input);
		final Theory theory = input.getTheory();
		assert impliesTerm.getFunction().getName() == "=>";
		final Term[] args = impliesTerm.getParameters();
		final Term[] newArgs = new Term[args.length];
		// We move the conclusion in front (see Simplify tech report)
		newArgs[0] = args[args.length - 1];
		for (int i = 1; i < newArgs.length; i++) {
			newArgs[i] = theory.term("not", args[i - 1]);
		}
		final Term rhs = theory.term("or", newArgs);
		final Term impliesRewrite = mTracker.buildRewrite(impliesTerm, rhs, ProofConstants.RW_IMP_TO_OR);
		return convertOrNot(mTracker.transitivity(input, impliesRewrite));
	}
}
