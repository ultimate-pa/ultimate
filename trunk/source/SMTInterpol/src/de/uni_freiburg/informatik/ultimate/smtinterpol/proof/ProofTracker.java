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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier.ConditionChain;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Utils;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class ProofTracker implements IProofTracker {

	private static class Rewrite {
		Rewrite mNext;

		public Term toTerm() {
			throw new InternalError("toTerm called on sentinel");
		}
	}

	private static class ExpandRewrite extends Rewrite {
		ApplicationTerm mOld;

		public ExpandRewrite(Term old) {
			mOld = (ApplicationTerm) old;
		}

		@Override
		public Term toTerm() {
			// We've never produced the new value, hence we have to produce it
			// here
			final FunctionSymbol fsym = mOld.getFunction();
			final Term[] params = mOld.getParameters();
			final Theory t = mOld.getTheory();
			Term res;
			if (fsym.isLeftAssoc()) {
				res = t.term(fsym, params[0], params[1]);
				for (int i = 2; i < params.length; ++i) {
					res = t.term(fsym, res, params[i]);
				}
			} else if (fsym.isRightAssoc()) {
				res = t.term(fsym, params[params.length - 2], params[params.length - 1]);
				for (int i = params.length - 3; i >= 0; --i) {
					res = t.term(fsym, params[i], res);
				}
			} else if (fsym.isChainable()) {
				res = t.term(fsym, params[0], params[1]);
				for (int i = 1; i < params.length - 1; ++i) {
					res = t.term(t.mAnd, res, t.term(fsym, params[i], params[i + 1]));
				}
			} else {
				throw new InternalError("Cannot expand " + fsym);
			}
			res = t.annotatedTerm(new Annotation[] { ProofConstants.REWRITEANNOTS[ProofConstants.RW_EXPAND] },
					t.term("=", mOld, res));
			return t.term("@rewrite", res);
		}
	}

	private static class ResultRewrite extends Rewrite {
		Term mOld;
		Term mNew;
		int mNum;

		public ResultRewrite(Term oldTerm, Term newTerm, int rewriteNum) {
			mOld = SMTAffineTerm.cleanup(oldTerm);
			mNew = SMTAffineTerm.cleanup(newTerm);
			mNum = rewriteNum;
			// assert (oldTerm != newTerm) : "ResultRewrite should track changes";
		}

		@Override
		public Term toTerm() {
			final Theory t = mOld.getTheory();
			Term base = t.term("=", mOld, mNew);
			base = t.annotatedTerm(new Annotation[] { ProofConstants.REWRITEANNOTS[mNum] }, base);
			return t.term("@rewrite", base);
		}
	}

	private static class RemoveConnective extends Rewrite {
		private final int mRule;
		private final Term[] mArgs;
		private final Term mRes;

		public RemoveConnective(int rule, Term[] args, Term res) {
			mRule = rule;
			/*
			 * If rule is RW_AND_TO_OR, we are called from createAndInplace. We have to clone the args since they get
			 * changed!
			 */
			mArgs = rule == ProofConstants.RW_AND_TO_OR ? args.clone() : args;
			mRes = res;
		}

		@Override
		public Term toTerm() {
			final Theory t = mArgs[0].getTheory();
			Term orig, res;
			Term[] resArgs = mArgs;
			switch (mRule) {
			case ProofConstants.RW_AND_TO_OR:
				resArgs = new Term[mArgs.length];
				orig = t.term(t.mAnd, mArgs);
				for (int i = 0; i < resArgs.length; ++i) {
					resArgs[i] = t.term(t.mNot, mArgs[i]);
				}
				res = t.term(t.mNot, t.term(t.mOr, resArgs));
				break;
			case ProofConstants.RW_XOR_TO_DISTINCT:
				orig = t.term(t.mXor, mArgs);
				res = t.term("distinct", resArgs);
				break;
			case ProofConstants.RW_IMP_TO_OR:
				resArgs = new Term[resArgs.length];
				orig = t.term(t.mImplies, mArgs);
				for (int i = 1; i < resArgs.length; ++i) {
					resArgs[i] = t.term(t.mNot, mArgs[i - 1]);
				}
				resArgs[0] = mArgs[mArgs.length - 1];
				res = t.term(t.mOr, resArgs);
				break;
			case ProofConstants.RW_LEQ_TO_LEQ0:
				orig = t.term("<=", mArgs);
				resArgs = new Term[2];
				resArgs[0] = SMTAffineTerm.cleanup(mRes);
				resArgs[1] = resArgs[0].getSort().getName().equals("Int") ? t.numeral(BigInteger.ZERO)
						: t.decimal(BigDecimal.ZERO);
				res = t.term("<=", resArgs);
				break;
			case ProofConstants.RW_GEQ_TO_LEQ0:
				orig = t.term(">=", mArgs);
				resArgs = new Term[2];
				resArgs[0] = SMTAffineTerm.cleanup(mRes);
				resArgs[1] = resArgs[0].getSort().getName().equals("Int") ? t.numeral(BigInteger.ZERO)
						: t.decimal(BigDecimal.ZERO);
				res = t.term("<=", resArgs);
				break;
			case ProofConstants.RW_GT_TO_LEQ0:
				orig = t.term(">", mArgs);
				resArgs = new Term[2];
				resArgs[0] = SMTAffineTerm.cleanup(mRes);
				resArgs[1] = resArgs[0].getSort().getName().equals("Int") ? t.numeral(BigInteger.ZERO)
						: t.decimal(BigDecimal.ZERO);
				res = t.term(t.mNot, t.term("<=", resArgs));
				break;
			case ProofConstants.RW_LT_TO_LEQ0:
				orig = t.term("<", mArgs);
				resArgs = new Term[2];
				resArgs[0] = SMTAffineTerm.cleanup(mRes);
				resArgs[1] = resArgs[0].getSort().getName().equals("Int") ? t.numeral(BigInteger.ZERO)
						: t.decimal(BigDecimal.ZERO);
				res = t.term(t.mNot, t.term("<=", resArgs));
				break;
			default:
				throw new InternalError("BUG in ProofTracker: RemoveConnective");
			}
			res = t.annotatedTerm(new Annotation[] { ProofConstants.REWRITEANNOTS[mRule] }, t.term("=", orig, res));
			return t.term("@rewrite", res);
		}
	}

	private static class InternRewrite extends Rewrite {
		private final Term mTerm, mLitTerm;

		public InternRewrite(Term term, Term litTerm) {
			assert (term != litTerm) : "Intern should track changes!!!";
			mTerm = term;
			mLitTerm = litTerm;
		}

		@Override
		public Term toTerm() {
			final Theory t = mTerm.getTheory();
			final Term res = t.term("=", mTerm, mLitTerm);
			return t.term("@intern", res);
		}
	}

	private final Rewrite mFirst;
	private Rewrite mLast, mMarkPos, mSave;
	private int mNumRewrites = 0, mSaveNumRewrites;

	private Map<Term, Term> mLits;

	private boolean addToLits(Term orig, Term lit) {
		if (mLits == null) {
			mLits = new HashMap<Term, Term>();
		}
		return mLits.put(orig, lit) == null;
	}

	private void prepend(Rewrite rw) {
		assert invNumRewrites();
		rw.mNext = mFirst.mNext;
		mFirst.mNext = rw;
		if (rw.mNext == null) {
			mLast = rw;
		}
		++mNumRewrites;
		assert invNumRewrites();
	}

	private void append(Rewrite rw) {
		assert invNumRewrites();
		mLast.mNext = rw;
		mLast = rw;
		++mNumRewrites;
		assert invNumRewrites();
	}

	private void insertAtMarkedPos(Rewrite rw) {
		assert invNumRewrites();
		rw.mNext = mMarkPos.mNext;
		mMarkPos.mNext = rw;
		++mNumRewrites;
		if (mMarkPos == mLast) {
			mLast = rw;
		}
		assert invNumRewrites();
	}

	private boolean invNumRewrites() {
		int i = 0;
		for (Rewrite rw = mFirst.mNext; rw != null; rw = rw.mNext) {
			++i;
		}
		assert i == mNumRewrites;
		return i == mNumRewrites;
	}

	public ProofTracker() {
		mFirst = mLast = mMarkPos = new Rewrite();
	}

	@Override
	public void reset() {
		mFirst.mNext = null;
		mLast = mMarkPos = mFirst;
		mNumRewrites = 0;
		assert invNumRewrites();
	}

	@Override
	public void expand(ApplicationTerm orig) {
		prepend(new ExpandRewrite(orig));
	}

	@Override
	public void expandDef(Term orig, Term res) {
		prepend(new ResultRewrite(orig, res, ProofConstants.RW_EXPAND_DEF));
	}

	@Override
	public void equality(Term[] args, Object res, int rule) {
		Term tres = null;
		if (res instanceof Term) {
			tres = (Term) res;
		} else {
			final Theory t = args[0].getTheory();
			assert res instanceof Term[];
			final Term[] resArgs = (Term[]) res;
			if (resArgs.length == 0) {
				tres = t.mTrue;
			} else if (resArgs.length == 1) {
				tres = rule == ProofConstants.RW_EQ_FALSE ? t.term(t.mNot, resArgs[0]) : resArgs[0];
			} else if (rule == ProofConstants.RW_EQ_TRUE) {
				// We use inplace algorithms. So clone the array.
				tres = t.term(t.mAnd, resArgs.clone());
			} else if (rule == ProofConstants.RW_EQ_FALSE) {
				tres = t.term(t.mNot, t.term(t.mOr, resArgs));
			} else if (rule == ProofConstants.RW_EQ_SIMP) {
				tres = t.term("=", resArgs);
			} else {
				throw new InternalError("Strange result in equality rewrite");
			}
		}
		append(new ResultRewrite(tres.getTheory().term("=", args), tres, rule));
	}

	@Override
	public void distinct(Term[] args, Term res, int rule) {
		if (res == null) {
			final Theory t = args[0].getTheory();
			if (rule == ProofConstants.RW_DISTINCT_TRUE) {
				if (args[0] == t.mTrue) {
					res = t.term(t.mNot, args[1]);
				} else {
					res = t.term(t.mNot, args[0]);
				}
			} else {
				throw new InternalError("Result should be given");
			}
		}
		append(new ResultRewrite(res.getTheory().term("distinct", args), res, rule));
	}

	@Override
	public void negation(Term pos, Term res, int rule) {
		final Theory t = res.getTheory();
		append(new ResultRewrite(t.term(t.mNot, pos), res, rule));
	}

	@Override
	public void or(Term[] args, Term res, int rule) {
		append(new ResultRewrite(res.getTheory().term("or", args), res, rule));
	}

	@Override
	public void ite(Term cond, Term thenTerm, Term elseTerm, Term res, int rule) {
		final Theory t = cond.getTheory();
		if (res == null) {
			switch (rule) {
			case ProofConstants.RW_ITE_BOOL_2:
				res = t.term(t.mNot, cond);
				break;
			case ProofConstants.RW_ITE_BOOL_4:
				res = t.term(t.mNot, t.term(t.mOr, cond, t.term(t.mNot, elseTerm)));
				break;
			case ProofConstants.RW_ITE_BOOL_5:
				res = t.term(t.mOr, t.term(t.mNot, cond), thenTerm);
				break;
			case ProofConstants.RW_ITE_BOOL_6:
				res = t.term(t.mNot, t.term(t.mOr, t.term(t.mNot, cond), t.term(t.mNot, thenTerm)));
				break;
			default:
				throw new InternalError("BUG in ProofTracker: ITE");
			}
		}
		append(new ResultRewrite(t.term("ite", cond, thenTerm, elseTerm), res, rule));
	}

	@Override
	public void strip(AnnotatedTerm orig) {
		prepend(new ResultRewrite(orig, orig.getSubterm(), ProofConstants.RW_STRIP));
	}

	@Override
	public void sum(FunctionSymbol fsym, Term[] args, Term res) {
		final Theory t = fsym.getTheory();
		final Term left = SMTAffineTerm.cleanup(t.term(fsym, args));
		final Term right = SMTAffineTerm.cleanup(res);
		if (left != right) {
			append(new ResultRewrite(left, right, ProofConstants.RW_CANONICAL_SUM));
		}
	}

	@Override
	public void leqSimp(SMTAffineTerm leq, Term res, int rule) {
		final Theory t = res.getTheory();
		final Term left = t.term("<=", SMTAffineTerm.cleanup(leq),
				leq.getSort().getName().equals("Int") ? t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO));
		append(new ResultRewrite(left, res, rule));
	}

	@Override
	public void desugar(ApplicationTerm orig, Term[] origArgs, Term[] newArgs) {
		final Theory t = orig.getTheory();
		append(new ResultRewrite(t.term(orig.getFunction(), origArgs), t.term(orig.getFunction(), newArgs),
				ProofConstants.RW_DESUGAR));
	}

	@Override
	public void divisible(FunctionSymbol divn, Term div, Term res) {
		final Term divisible = res.getTheory().term(divn, SMTAffineTerm.cleanup(div));
		append(new ResultRewrite(divisible, res, ProofConstants.RW_DIVISIBLE));
	}

	@Override
	public Term getRewriteProof(Term asserted) {
		assert invNumRewrites();
		final Theory t = asserted.getTheory();
		return getEqProof(t.term("@asserted", asserted));
	}

	private Term getEqProof(Term proofPart) {
		if (mNumRewrites == 0) {
			return proofPart;
		}
		final Term[] args = new Term[mNumRewrites + 1];
		args[0] = proofPart;
		int i = 1;
		for (Rewrite rw = mFirst.mNext; rw != null; rw = rw.mNext) {
			args[i++] = rw.toTerm();
		}
		final Term eq = proofPart.getTheory().term("@eq", args);
		return eq;
	}

	@Override
	public void distinctBoolEq(Term lhs, Term rhs, boolean firstNegated) {
		final Theory t = lhs.getTheory();
		final Term distinct = t.term("distinct", lhs, rhs);
		final Term res = firstNegated ? t.term("=", t.term(t.mNot, lhs), rhs) : t.term("=", lhs, t.term(t.mNot, rhs));
		append(new ResultRewrite(distinct, res, ProofConstants.RW_DISTINCT_BOOL_EQ));
	}

	@Override
	public void removeConnective(Term[] origArgs, Term result, int rule) {
		if (rule == ProofConstants.RW_LEQ_TO_LEQ0) {
			assert (origArgs.length == 2);
			final SMTAffineTerm constant = SMTAffineTerm.create(origArgs[1]);
			if (constant.isConstant() && constant.getConstant().equals(Rational.ZERO)) {
				final Term tmp = SMTAffineTerm.cleanup(result);
				final Term tmp2 = SMTAffineTerm.cleanup(origArgs[0]);
				if (tmp == tmp2) {
					return;
				}
			}
		}
		append(new RemoveConnective(rule, origArgs, result));
	}

	@Override
	public void quoted(Term orig, Literal quote) {
		final Term t = quote.getSMTFormula(orig.getTheory(), true);
		append(new InternRewrite(orig, t));
	}

	@Override
	public void eq(Term lhs, Term rhs, Term res) {
		final Term orig = res.getTheory().term("=", lhs, rhs);
		if (orig != res) {
			append(new InternRewrite(orig, res));
		}
	}

	@Override
	public void eq(Term lhs, Term rhs, DPLLAtom eqAtom) {
		final Theory t = lhs.getTheory();
		final Term res = SMTAffineTerm.cleanup(eqAtom.getSMTFormula(t, true));
		final Term orig = SMTAffineTerm.cleanup(t.term("=", lhs, rhs));
		if (orig != res) {
			append(new InternRewrite(orig, res));
		}

	}

	@Override
	public void leq0(SMTAffineTerm sum, Literal lit) {
		final Theory t = sum.getTheory();
		final Term orig = t.term("<=", SMTAffineTerm.cleanup(sum),
				sum.getSort().getName().equals("Int") ? t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO));
		final Term res = lit.getSMTFormula(t, true);
		if (orig != res) {
			append(new InternRewrite(orig, res));
		}
	}

	@Override
	public void intern(Term term, Literal lit) {
		final Theory t = term.getTheory();
		final Term orig = SMTAffineTerm.cleanup(term);
		final Term res = lit.getSMTFormula(t, true);
		if (orig != res) {
			append(new InternRewrite(orig, res));
		}
	}

	@Override
	public Term split(Term data, Term proof, int splitKind) {
		final Theory t = proof.getTheory();
		Term res;
		switch (splitKind) {
		case ProofConstants.SPLIT_NEG_OR:
			// data has to be negated here...
			// if data is already a negation, we have to rewrite the potential
			// double negation.
			res = t.term(t.mNot, data);
			Term base = t.term("@split",
					t.annotatedTerm(new Annotation[] { ProofConstants.SPLITANNOTS[splitKind] }, proof), res);
			Term posRes = res;
			if (Utils.isNegation(data)) {
				posRes = ((ApplicationTerm) data).getParameters()[0];
				final Term rewrite = t.term("@rewrite",
						t.annotatedTerm(new Annotation[] { ProofConstants.REWRITEANNOTS[ProofConstants.RW_NOT_SIMP] },
								t.term("=", res, posRes)));
				base = t.term("@eq", base, rewrite);
			}
			return base;
		case ProofConstants.SPLIT_POS_EQ_1:
			Term[] params = ((ApplicationTerm) data).getParameters();
			assert params.length == 2;
			res = t.term(t.mOr, params[0], t.term(t.mNot, params[1]));
			break;
		case ProofConstants.SPLIT_POS_EQ_2:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 2;
			res = t.term(t.mOr, t.term(t.mNot, params[0]), params[1]);
			break;
		case ProofConstants.SPLIT_NEG_EQ_1:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 2;
			res = t.term(t.mOr, params);
			break;
		case ProofConstants.SPLIT_NEG_EQ_2:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 2;
			res = t.term(t.mOr, t.term(t.mNot, params[0]), t.term(t.mNot, params[1]));
			break;
		case ProofConstants.SPLIT_POS_ITE_1:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 3; // NOCHECKSTYLE since ite has 3 params
			res = t.term(t.mOr, t.term(t.mNot, params[0]), params[1]);
			break;
		case ProofConstants.SPLIT_POS_ITE_2:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 3; // NOCHECKSTYLE since ite has 3 params
			res = t.term(t.mOr, params[0], params[2]);
			break;
		case ProofConstants.SPLIT_NEG_ITE_1:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 3; // NOCHECKSTYLE since ite has 3 params
			res = t.term(t.mOr, t.term(t.mNot, params[0]), t.term(t.mNot, params[1]));
			break;
		case ProofConstants.SPLIT_NEG_ITE_2:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 3; // NOCHECKSTYLE since ite has 3 params
			res = t.term(t.mOr, params[0], t.term(t.mNot, params[2]));
			break;
		default:
			throw new InternalError("BUG in ProofTracker: Split");
		}
		return getEqProof(t.term("@split",
				t.annotatedTerm(new Annotation[] { ProofConstants.SPLITANNOTS[splitKind] }, proof), res));
	}

	@Override
	public Term clause(Term proof) {
		assert invNumRewrites();
		return getEqProof(proof);
	}

	@Override
	public Term auxAxiom(int auxKind, Literal auxLit, Term data, Term base, Object auxData) {
		final Theory t = data.getTheory();
		Term axiom;
		switch (auxKind) {
		case ProofConstants.AUX_TRUE_NOT_FALSE:
			// auxLit is (not (= true false)), i.e., it has negative polarity
			axiom = auxLit.getSMTFormula(t, true);
			break;
		case ProofConstants.AUX_OR_POS: {
			final Term[] args = ((ApplicationTerm) data).getParameters();
			final Term[] nargs = new Term[args.length + 1];
			nargs[0] = t.term(t.mNot, auxLit.getSMTFormula(t, true));
			System.arraycopy(args, 0, nargs, 1, args.length);
			axiom = t.term(t.mOr, nargs);
			break;
		}
		case ProofConstants.AUX_OR_NEG:
			axiom = t.term(t.mOr, auxLit.getSMTFormula(t, true), t.term(t.mNot, data));
			break;
		case ProofConstants.AUX_ITE_POS_1:
			Term[] params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.mOr, t.term(t.mNot, auxLit.getSMTFormula(t, true)), t.term(t.mNot, params[0]), params[1]);
			break;
		case ProofConstants.AUX_ITE_POS_2:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.mOr, t.term(t.mNot, auxLit.getSMTFormula(t, true)), params[0], params[2]);
			break;
		case ProofConstants.AUX_ITE_POS_RED:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.mOr, t.term(t.mNot, auxLit.getSMTFormula(t, true)), params[1], params[2]);
			break;
		case ProofConstants.AUX_ITE_NEG_1:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.mOr, auxLit.getSMTFormula(t, true), t.term(t.mNot, params[0]), t.term(t.mNot, params[1]));
			break;
		case ProofConstants.AUX_ITE_NEG_2:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.mOr, auxLit.getSMTFormula(t, true), params[0], t.term(t.mNot, params[2]));
			break;
		case ProofConstants.AUX_ITE_NEG_RED:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.mOr, auxLit.getSMTFormula(t, true), t.term(t.mNot, params[1]), t.term(t.mNot, params[2]));
			break;
		case ProofConstants.AUX_EQ_POS_1:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.mOr, t.term(t.mNot, auxLit.getSMTFormula(t, true)), params[0], t.term(t.mNot, params[1]));
			break;
		case ProofConstants.AUX_EQ_POS_2:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.mOr, t.term(t.mNot, auxLit.getSMTFormula(t, true)), t.term(t.mNot, params[0]), params[1]);
			break;
		case ProofConstants.AUX_EQ_NEG_1:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.mOr, auxLit.getSMTFormula(t, true), params[0], params[1]);
			break;
		case ProofConstants.AUX_EQ_NEG_2:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.mOr, auxLit.getSMTFormula(t, true), t.term(t.mNot, params[0]), t.term(t.mNot, params[1]));
			break;
		case ProofConstants.AUX_EXCLUDED_MIDDLE_1:
			axiom = t.term(t.mOr, t.term(t.mNot, data), auxLit.getSMTFormula(t, true));
			break;
		case ProofConstants.AUX_EXCLUDED_MIDDLE_2:
			axiom = t.term(t.mOr, data, auxLit.getSMTFormula(t, true));
			break;
		case ProofConstants.AUX_TERM_ITE:
			final ConditionChain tmp = (ConditionChain) auxData;
			// Determine size
			ConditionChain walk = tmp;
			int size = 1;
			while (walk != null) {
				walk = walk.getPrevious();
				++size;
			}
			final Term[] nparams = new Term[size];
			walk = tmp;
			for (int i = size - 2; i >= 0; --i) {
				nparams[i] = t.term(t.mNot, walk.getTerm());
				if (Utils.isNegation(walk.getTerm())) {
					negation(walk.getTerm(), Utils.createNotUntracked(walk.getTerm()), ProofConstants.RW_NOT_SIMP);
				}
				walk = walk.getPrevious();
			}
			nparams[size - 1] = t.term("=", base, data);
			axiom = t.term(t.mOr, nparams);
			break;
		case ProofConstants.AUX_DIV_LOW:
			axiom = t.term("<=", SMTAffineTerm.cleanup(data), t.numeral(BigInteger.ZERO));
			break;
		case ProofConstants.AUX_TO_INT_LOW:
			axiom = t.term("<=", SMTAffineTerm.cleanup(data), t.rational(BigInteger.ZERO, BigInteger.ONE));
			break;
		case ProofConstants.AUX_DIV_HIGH:
			axiom = t.term(t.mNot, t.term("<=", SMTAffineTerm.cleanup(data), t.numeral(BigInteger.ZERO)));
			break;
		case ProofConstants.AUX_TO_INT_HIGH:
			axiom = t.term(t.mNot,
					t.term("<=", SMTAffineTerm.cleanup(data), t.rational(BigInteger.ZERO, BigInteger.ONE)));
			break;
		case ProofConstants.AUX_ARRAY_STORE:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term("=", t.term("select", data, params[1]), params[2]);
			break;
		case ProofConstants.AUX_ARRAY_DIFF:
			// Create a = b \/ select(a, diff(a,b)) != select(b, diff(a,b))
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term("or", t.term("=", params),
					t.term("not", t.term("=", t.term("select", params[0], data), t.term("select", params[1], data))));
			break;
		default:
			throw new InternalError("BUG in ProofTracker: AUX");
		}
		return t.term("@tautology", t.annotatedTerm(new Annotation[] { ProofConstants.AUXANNOTS[auxKind] }, axiom));
	}

	@Override
	public IProofTracker getDescendent() {
		return new ProofTracker();
	}

	@Override
	public void modulo(ApplicationTerm appTerm, Term res) {
		append(new ResultRewrite(appTerm, res, ProofConstants.RW_MODULO));
	}

	@Override
	public void mod(Term x, Term y, Term res, int rule) {
		final Theory t = x.getTheory();
		final Term mod = t.term("mod", SMTAffineTerm.cleanup(x), SMTAffineTerm.cleanup(y));
		append(new ResultRewrite(mod, SMTAffineTerm.cleanup(res), rule));
	}

	@Override
	public void div(Term x, Term y, Term res, int rule) {
		final Theory t = x.getTheory();
		final Term mod = t.term("div", SMTAffineTerm.cleanup(x), SMTAffineTerm.cleanup(y));
		append(new ResultRewrite(mod, SMTAffineTerm.cleanup(res), rule));
	}

	@Override
	public void toInt(Term arg, Term res) {
		final Theory t = arg.getTheory();
		final Term toint = t.term("to_int", SMTAffineTerm.cleanup(arg));
		append(new ResultRewrite(toint, SMTAffineTerm.cleanup(res), ProofConstants.RW_TO_INT));
	}

	@Override
	public Term[] prepareIRAHack(Term[] args) {
		return args.clone();
	}

	@Override
	public void negateLit(Literal lit, Theory theory) {
		assert lit.getSign() == -1 : "Literal not negated!";
		final Term lhs = theory.term(theory.mNot, SMTAffineTerm.cleanup(lit.getSMTFormula(theory, true)));
		final Term rhs = SMTAffineTerm.cleanup(lit.getAtom().getSMTFormula(theory, true));
		append(new ResultRewrite(lhs, rhs, ProofConstants.RW_NOT_SIMP));
	}

	@Override
	public void arrayRewrite(Term[] args, Term result, int rule) {
		final Theory t = result.getTheory();
		final Term input = rule == ProofConstants.RW_STORE_OVER_STORE ? t.term("store", args) : t.term("select", args);
		append(new ResultRewrite(input, result, rule));
	}

	private final static class FlattenHelper {
		private final Term[] mArgs;
		private int mOffset;

		public FlattenHelper(Term[] args, int offset) {
			mArgs = args;
			mOffset = offset;
		}

		public void flatten(ArrayDeque<FlattenHelper> todo, ArrayList<Term> args) {
			for (int i = mOffset; i < mArgs.length; ++i) {
				if (mArgs[i] instanceof ApplicationTerm) {
					final ApplicationTerm tst = (ApplicationTerm) mArgs[i];
					if (Clausifier.shouldFlatten(tst)) {
						mOffset = i + 1;
						if (mOffset < mArgs.length) {
							todo.addFirst(this);
						}
						todo.addFirst(new FlattenHelper(tst.getParameters(), 0));
						return;
					}
				}
				args.add(mArgs[i]);
			}
		}
	}

	@Override
	public void flatten(Term[] args, boolean simpOr) {
		final Theory t = args[0].getTheory();
		final ArrayDeque<FlattenHelper> toFlatten = new ArrayDeque<FlattenHelper>();
		toFlatten.add(new FlattenHelper(args, 0));
		final ArrayList<Term> newArgs = new ArrayList<Term>();
		while (!toFlatten.isEmpty()) {
			final FlattenHelper fh = toFlatten.poll();
			fh.flatten(toFlatten, newArgs);
		}
		final ApplicationTerm res = t.term(t.mOr, newArgs.toArray(new Term[newArgs.size()]));
		if (simpOr) {
			orSimpClause(res.getParameters());
		}
		insertAtMarkedPos(new ResultRewrite(t.term(t.mOr, args), res, ProofConstants.RW_FLATTEN));
	}

	@Override
	public void orSimpClause(Term[] args) {
		final Theory t = args[0].getTheory();
		final Term[] newArgs = args.clone();
		final LinkedHashSet<Term> clause = new LinkedHashSet<Term>();
		for (int i = 0; i < newArgs.length; ++i) {
			final Term tmp = SMTAffineTerm.cleanup(newArgs[i]);
			Term newDisj = mLits.get(tmp);
			/*
			 * This is the case for proxy literals in aux-clauses. They cannot merge since otherwise the term would be
			 * infinite because the term would be its own proper subterm.
			 */
			if (newDisj == null) {
				newDisj = tmp;
			}
			newArgs[i] = newDisj;
			if (newDisj != t.mFalse) {
				clause.add(newDisj);
			}
		}
		Term res;
		if (clause.isEmpty()) {
			res = t.mFalse;
		} else if (clause.size() == 1) {
			res = clause.iterator().next();
		} else {
			res = t.term(t.mOr, clause.toArray(new Term[clause.size()]));
		}
		final Rewrite rw = new ResultRewrite(t.term(t.mOr, newArgs), res, ProofConstants.RW_OR_SIMP);
		append(rw);
	}

	@Override
	public void markPosition() {
		mMarkPos = mLast;
	}

	@Override
	public Term[] produceAuxAxiom(Literal auxlit, Term... args) {
		final Theory t = args[0].getTheory();
		final Term[] res = new Term[1 + args.length];
		res[0] = auxlit.getSMTFormula(t, true);
		System.arraycopy(args, 0, res, 1, args.length);
		return res;
	}

	@Override
	public void save() {
		mSave = mLast;
		mSaveNumRewrites = mNumRewrites;
	}

	@Override
	public void restore() {
		if (mSave != null) {
			mLast = mSave;
			mLast.mNext = null;
			mNumRewrites = mSaveNumRewrites;
			mSave = null;
		}
		assert invNumRewrites();
	}

	@Override
	public void cleanSave() {
		mSave = null;
	}

	@Override
	public void normalized(ConstantTerm term, SMTAffineTerm res) {
		final Term rhs = SMTAffineTerm.cleanup(res);
		if (term != rhs) {
			append(new ResultRewrite(term, rhs, ProofConstants.RW_CANONICAL_SUM));
		}
	}

	@Override
	public boolean notifyLiteral(Literal lit, Term t) {
		return addToLits(SMTAffineTerm.cleanup(t), SMTAffineTerm.cleanup(lit.getSMTFormula(t.getTheory(), true)));
	}

	@Override
	public void notifyFalseLiteral(Term t) {
		addToLits(SMTAffineTerm.cleanup(t), t.getTheory().mFalse);
	}

	@Override
	public void storeRewrite(ApplicationTerm store, Term result, boolean arrayFirst) {
		final Term array = store.getParameters()[0];
		final Term orig =
				arrayFirst ? store.getTheory().term("=", array, store) : store.getTheory().term("=", store, array);
		append(new ResultRewrite(orig, result, ProofConstants.RW_STORE_REWRITE));
	}

	@Override
	public void toReal(Term arg, Term res) {
		final Term orig = arg.getTheory().term("to_real", SMTAffineTerm.cleanup(arg));
		append(new ResultRewrite(orig, SMTAffineTerm.cleanup(res), ProofConstants.RW_TO_REAL));
	}
}
