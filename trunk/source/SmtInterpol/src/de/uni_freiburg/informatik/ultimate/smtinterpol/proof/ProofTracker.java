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
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier.ConditionChain;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Utils;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class ProofTracker implements IProofTracker {

	private static class Rewrite {
		Rewrite m_Next;
		public Term toTerm() {
			throw new InternalError("toTerm called on sentinel");
		}
	}
	
	private static class ExpandRewrite extends Rewrite {
		ApplicationTerm m_Old;
		public ExpandRewrite(Term old) {
			m_Old = (ApplicationTerm) old;
		}
		@Override
		public Term toTerm() {
			// We've never produced the new value, hence we have to produce it
			// here
			FunctionSymbol fsym = m_Old.getFunction();
			Term[] params = m_Old.getParameters();
			Theory t = m_Old.getTheory();
			Term res;
			if (fsym.isLeftAssoc()) {
				res = t.term(fsym, params[0], params[1]);
				for (int i = 2; i < params.length; ++i)
					res = t.term(fsym, res, params[i]);
			} else if (fsym.isRightAssoc()) {
				res = t.term(fsym,
						params[params.length - 2], params[params.length - 1]);
				for (int i = params.length - 3; i >= 0; --i)
					res = t.term(fsym, params[i], res);
			} else if (fsym.isChainable()) {
				res = t.term(fsym, params[0], params[1]);
				for (int i = 1; i < params.length -1; ++i)
					res = t.term(t.m_And, res,
							t.term(fsym, params[i], params[i+1]));
			} else
				throw new InternalError("Cannot expand " + fsym);
			res = t.annotatedTerm(new Annotation[] {
					ProofConstants.REWRITEANNOTS[ProofConstants.RW_EXPAND]
				}, t.term("=", m_Old, res));
			return t.term("@rewrite", res);
		}
	}
	
	private static class ResultRewrite extends Rewrite {
		Term m_Old;
		Term m_New;
		int m_Num;
		public ResultRewrite(Term oldTerm, Term newTerm, int rewriteNum) {
			m_Old = SMTAffineTerm.cleanup(oldTerm);
			m_New = SMTAffineTerm.cleanup(newTerm);
			m_Num = rewriteNum;
			assert(oldTerm != newTerm) : "ResultRewrite should track changes";
		}
		@Override
		public Term toTerm() {
			Theory t = m_Old.getTheory();
			Term base = t.term("=", m_Old, m_New);
			base = t.annotatedTerm(new Annotation[] {
					ProofConstants.REWRITEANNOTS[m_Num]
				}, base);
			return t.term("@rewrite", base);
		}
	}
	
	private static class RemoveConnective extends Rewrite {
		private int m_Rule;
		private Term[] m_Args;
		private Term m_Res;
		public RemoveConnective(int rule, Term[] args, Term res) {
			m_Rule = rule;
			m_Args = args;
			m_Res = res;
			if (rule == ProofConstants.RW_AND_TO_OR)
				/* In this case, we are called from createAndInplace.  We have
				 * to clone the args since they get changed!
				 */
				m_Args = m_Args.clone();
		}
		@Override
		public Term toTerm() {
			Theory t = m_Args[0].getTheory();
			Term orig, res;
			Term[] resArgs = m_Args;
			switch(m_Rule) {
			case ProofConstants.RW_AND_TO_OR:
				resArgs = new Term[m_Args.length];
				orig = t.term(t.m_And, m_Args);
				for (int i = 0; i < resArgs.length; ++i)
					resArgs[i] = t.term(t.m_Not, m_Args[i]);
				res = t.term(t.m_Not, t.term(t.m_Or, resArgs));
				break;
			case ProofConstants.RW_XOR_TO_DISTINCT:
				orig = t.term(t.m_Xor, m_Args);
				res = t.term("distinct", resArgs);
				break;
			case ProofConstants.RW_IMP_TO_OR:
				resArgs = new Term[resArgs.length];
				orig = t.term(t.m_Implies, m_Args);
				for (int i = 1; i < resArgs.length; ++i)
					resArgs[i] = t.term(t.m_Not, m_Args[i - 1]);
				resArgs[0] = m_Args[m_Args.length - 1];
				res = t.term(t.m_Or, resArgs);
				break;
			case ProofConstants.RW_LEQ_TO_LEQ0:
				orig = t.term("<=", m_Args);
				resArgs = new Term[2];
				resArgs[0] = SMTAffineTerm.cleanup(m_Res);
				resArgs[1] = resArgs[0].getSort().getName().equals("Int") ?
						t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO);
				res = t.term("<=", resArgs);
				break;
			case ProofConstants.RW_GEQ_TO_LEQ0:
				orig = t.term(">=", m_Args);
				resArgs = new Term[2];
				resArgs[0] = SMTAffineTerm.cleanup(m_Res);
				resArgs[1] = resArgs[0].getSort().getName().equals("Int") ?
						t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO);
				res = t.term("<=", resArgs);
				break;
			case ProofConstants.RW_GT_TO_LEQ0:
				orig = t.term(">", m_Args);
				resArgs = new Term[2];
				resArgs[0] = SMTAffineTerm.cleanup(m_Res);
				resArgs[1] = resArgs[0].getSort().getName().equals("Int") ?
						t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO);
				res = t.term(t.m_Not, t.term("<=", resArgs));
				break;
			case ProofConstants.RW_LT_TO_LEQ0:
				orig = t.term("<", m_Args);
				resArgs = new Term[2];
				resArgs[0] = SMTAffineTerm.cleanup(m_Res);
				resArgs[1] = resArgs[0].getSort().getName().equals("Int") ?
						t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO);
				res = t.term(t.m_Not, t.term("<=", resArgs));
				break;
				default:
					throw new InternalError(
							"BUG in ProofTracker: RemoveConnective");
			}
			res = t.annotatedTerm(new Annotation[] {
					ProofConstants.REWRITEANNOTS[m_Rule]
				}, t.term("=", orig, res));
			return t.term("@rewrite", res);
		}
	}
	
	private static class InternRewrite extends Rewrite {
		private Term m_Term, m_LitTerm;
		public InternRewrite(Term term, Term litTerm) {
			assert (term != litTerm) : "Intern should track changes!!!";
			m_Term = term;
			m_LitTerm = litTerm;
		}
		@Override
		public Term toTerm() {
			Theory t = m_Term.getTheory();
			Term res = t.term("=", m_Term, m_LitTerm);
			return t.term("@intern", res);
		}
	}
	
	private Rewrite m_First, m_Last, m_MarkPos, m_Save;
	private int m_NumRewrites = 0, m_SaveNumRewrites;
	
	private Map<Term, Term> m_Lits;
	
	private boolean addToLits(Term orig, Term lit) {
		if (m_Lits == null)
			m_Lits = new HashMap<Term, Term>();
		return m_Lits.put(orig, lit) == null;
	}

	private void prepend(Rewrite rw) {
		assert(invNumRewrites());
		rw.m_Next = m_First.m_Next;
		m_First.m_Next = rw;
		if (rw.m_Next == null)
			m_Last = rw;
		++m_NumRewrites;
		assert(invNumRewrites());
	}
	
	private void append(Rewrite rw) {
		assert(invNumRewrites());
		m_Last.m_Next = rw;
		m_Last = rw;
		++m_NumRewrites;
		assert(invNumRewrites());
	}
	
	private void insertAtMarkedPos(Rewrite rw) {
		assert(invNumRewrites());
		rw.m_Next = m_MarkPos.m_Next;
		m_MarkPos.m_Next = rw;
		++m_NumRewrites;
		if (m_MarkPos == m_Last)
			m_Last = rw;
		assert(invNumRewrites());
	}
	
	private boolean invNumRewrites() {
		int i = 0;
		for (Rewrite rw = m_First.m_Next; rw != null; rw = rw.m_Next)
			++i;
		assert (i == m_NumRewrites);
		return i == m_NumRewrites;
	}
	
	public ProofTracker() {
		m_First = m_Last = m_MarkPos = new Rewrite();
	}

	@Override
	public void reset() {
		m_First.m_Next = null;
		m_Last = m_MarkPos = m_First;
		m_NumRewrites = 0;
		assert(invNumRewrites());
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
		if (!(res instanceof Term)) {
			Theory t = args[0].getTheory();
			assert res instanceof Term[];
			Term[] resArgs = (Term[]) res;
			if (resArgs.length == 0)
				tres = t.TRUE;
			else if (resArgs.length == 1)
				tres = rule == ProofConstants.RW_EQ_FALSE ? 
						t.term(t.m_Not, resArgs[0]) : resArgs[0];
			else if (rule == ProofConstants.RW_EQ_TRUE) {
				// We use inplace algorithms.  So clone the array.
				tres = t.term(t.m_And, resArgs.clone());
			} else if (rule == ProofConstants.RW_EQ_FALSE)
				tres = t.term(t.m_Not, t.term(t.m_Or, resArgs));
			else if (rule == ProofConstants.RW_EQ_SIMP)
				tres = t.term("=", resArgs);
			else
				throw new InternalError("Strange result in equality rewrite");
		} else
			tres = (Term) res;
		append(new ResultRewrite(tres.getTheory().term("=", args), tres, rule));
	}

	@Override
	public void distinct(Term[] args, Term res, int rule) {
		if (res == null) {
			Theory t = args[0].getTheory();
			if (rule == ProofConstants.RW_DISTINCT_TRUE) {
				if (args[0] == t.TRUE)
					res = t.term(t.m_Not, args[1]);
				else
					res = t.term(t.m_Not, args[0]);
			} else
				throw new InternalError("Result should be given");
		}
		append(new ResultRewrite(
				res.getTheory().term("distinct", args), res, rule));
	}

	@Override
	public void negation(Term pos, Term res, int rule) {
		Theory t = res.getTheory();
		append(new ResultRewrite(t.term(t.m_Not, pos), res, rule));
	}

	@Override
	public void or(Term[] args, Term res, int rule) {
		append(new ResultRewrite(res.getTheory().term("or", args), res, rule));
	}

	@Override
	public void ite(Term cond, Term thenTerm, Term elseTerm, Term res, int rule) {
		Theory t = cond.getTheory();
		if (res == null) {
			switch(rule) {
			case ProofConstants.RW_ITE_BOOL_2:
				res = t.term(t.m_Not, cond);
				break;
			case ProofConstants.RW_ITE_BOOL_4:
				res = t.term(t.m_Not, t.term(t.m_Or, cond,
						t.term(t.m_Not, elseTerm)));
				break;
			case ProofConstants.RW_ITE_BOOL_5:
				res = t.term(t.m_Or, t.term(t.m_Not, cond), thenTerm);
				break;
			case ProofConstants.RW_ITE_BOOL_6:
				res = t.term(t.m_Not,	t.term(t.m_Or, t.term(t.m_Not, cond),
						t.term(t.m_Not, thenTerm)));
				break;
				default:
					throw new InternalError("BUG in ProofTracker: ITE");
			}
		}
		append(new ResultRewrite(t.term("ite", cond, thenTerm, elseTerm),
				res, rule));
	}

	@Override
	public void strip(AnnotatedTerm orig) {
		prepend(new ResultRewrite(
				orig, orig.getSubterm(), ProofConstants.RW_STRIP));
	}

	@Override
	public void sum(FunctionSymbol fsym, Term[] args, Term res) {
		Theory t = fsym.getTheory();
		Term left = SMTAffineTerm.cleanup(t.term(fsym, args));
		Term right = SMTAffineTerm.cleanup(res);
		if (left != right)
			append(new ResultRewrite(
					left, right, ProofConstants.RW_CANONICAL_SUM));
	}

	@Override
	public void toLeq0(Term orig, SMTAffineTerm leq, int rule) {
		Theory t = orig.getTheory();
		Term right = t.term(
				"<=", SMTAffineTerm.cleanup(leq),
				leq.getSort().getName().equals("Int") ?
						t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO));
		if (rule == ProofConstants.RW_LT_TO_LEQ0 ||
				rule == ProofConstants.RW_GT_TO_LEQ0)
			right = t.term(t.m_Not, right);
		if (right != orig)
			append(new ResultRewrite(orig, right, rule));
	}

	@Override
	public void leqSimp(SMTAffineTerm leq, Term res, int rule) {
		Theory t = res.getTheory();
		Term left = t.term("<=", SMTAffineTerm.cleanup(leq),
				leq.getSort().getName().equals("Int") ?
						t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO));
		append(new ResultRewrite(left, res, rule));
	}

	@Override
	public void desugar(ApplicationTerm orig, Term[] origArgs, Term[] newArgs) {
		Theory t = orig.getTheory();
		append(new ResultRewrite(t.term(orig.getFunction(), origArgs),
				t.term(orig.getFunction(), newArgs),
				ProofConstants.RW_DESUGAR));
	}

	@Override
	public void divisible(FunctionSymbol divn, Term div, Term res) {
		Term divisible = res.getTheory().term(divn, SMTAffineTerm.cleanup(div));
		append(new ResultRewrite(divisible, res, ProofConstants.RW_DIVISIBLE));
	}

	@Override
	public Term getRewriteProof(Term asserted) {
		assert(invNumRewrites());
		Theory t = asserted.getTheory();
		return getEqProof(t.term("@asserted", asserted));
	}
	
	private Term getEqProof(Term proofPart) {
		if (m_NumRewrites == 0)
			return proofPart;
		Term[] args = new Term[m_NumRewrites + 1];
		args[0] = proofPart;
		int i = 1;
		for (Rewrite rw = m_First.m_Next; rw != null; rw = rw.m_Next)
			args[i++] = rw.toTerm();
		Term eq = proofPart.getTheory().term("@eq", args);
		return eq;
	}

	@Override
	public void distinctBinary(Term lhs, Term rhs, boolean firstNegated) {
		Theory t = lhs.getTheory();
		Term distinct = t.term("distinct", lhs, rhs);
		Term res = firstNegated ? t.term("=", t.term(t.m_Not, lhs), rhs) :
			t.term("=", lhs, t.term(t.m_Not, rhs));
		append(new ResultRewrite(
				distinct, res, ProofConstants.RW_DISTINCT_BINARY));
	}

	@Override
	public void removeConnective(Term[] origArgs, Term result, int rule) {
		if (rule == ProofConstants.RW_LEQ_TO_LEQ0) {
			assert(origArgs.length == 2);
			SMTAffineTerm constant = SMTAffineTerm.create(origArgs[1]);
			if (constant.isConstant() &&
					constant.getConstant().equals(Rational.ZERO)) {
				Term tmp = SMTAffineTerm.cleanup(result);
				Term tmp2 = SMTAffineTerm.cleanup(origArgs[0]);
				if (tmp == tmp2)
					return;
			}
		}
		append(new RemoveConnective(rule, origArgs, result));
	}

	@Override
	public void quoted(Term orig, Literal quote) {
		Term t = quote.getSMTFormula(orig.getTheory(), true);
		append(new InternRewrite(orig, t));
	}

	@Override
	public void eq(Term lhs, Term rhs, Term res) {
		Term orig = res.getTheory().term("=", lhs, rhs);
		if (orig != res)
			append(new InternRewrite(orig, res));
		if (res == res.getTheory().TRUE) {
			orig = res.getTheory().term("not", orig);
			res = res.getTheory().FALSE;
		}
	}

	@Override
	public void eq(Term lhs, Term rhs, DPLLAtom eqAtom) {
		Theory t = lhs.getTheory();
		Term res = SMTAffineTerm.cleanup(eqAtom.getSMTFormula(t, true));
		Term orig = SMTAffineTerm.cleanup(t.term("=", lhs, rhs));
		if (orig != res)
			append(new InternRewrite(orig, res));
		
	}

	@Override
	public void leq0(SMTAffineTerm sum, Literal lit) {
		Theory t = sum.getTheory();
		Term orig = t.term("<=", SMTAffineTerm.cleanup(sum),
				sum.getSort().getName().equals("Int") ?
						t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO));
		Term res = lit.getSMTFormula(t, true);
		if (orig != res)
			append(new InternRewrite(orig, res));
	}

	@Override
	public void intern(Term term, Literal lit) {
		Theory t = term.getTheory();
		Term orig = SMTAffineTerm.cleanup(term);
		Term res = lit.getSMTFormula(t, true);
		if (orig != res)
			append(new InternRewrite(orig, res));
	}
	
	@Override
	public Term split(Term data, Term proof, int splitKind) {
		Theory t = proof.getTheory();
		Term res;
		switch (splitKind) {
		case ProofConstants.SPLIT_NEG_OR:
			// data has to be negated here...
			// if data is already a negation, we have to rewrite the potential
			// double negation.
			res = t.term(t.m_Not, data);
			Term base = t.term("@split", t.annotatedTerm(
					new Annotation[] {ProofConstants.SPLITANNOTS[splitKind]},
					proof), res);
			Term posRes = res;
			if (Utils.isNegation(data)) {
				posRes = ((ApplicationTerm) data).getParameters()[0];
				Term rewrite = t.term("@rewrite", t.annotatedTerm(
						new Annotation[] {
								ProofConstants.REWRITEANNOTS[ProofConstants.RW_NOT_SIMP]
						},
						t.term("=", res, posRes)));
				base = t.term("@eq", base, rewrite);
			}
			return base;
		case ProofConstants.SPLIT_POS_EQ_1:
			Term[] params = ((ApplicationTerm) data).getParameters();
			assert params.length == 2;
			res = t.term(t.m_Or, params[0], t.term(t.m_Not, params[1]));
			break;
		case ProofConstants.SPLIT_POS_EQ_2:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 2;
			res = t.term(t.m_Or, t.term(t.m_Not, params[0]), params[1]);
			break;
		case ProofConstants.SPLIT_NEG_EQ_1:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 2;
			res = t.term(t.m_Or, params);
			break;
		case ProofConstants.SPLIT_NEG_EQ_2:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 2;
			res = t.term(t.m_Or, t.term(t.m_Not, params[0]),
					t.term(t.m_Not, params[1]));
			break;
		case ProofConstants.SPLIT_POS_ITE_1:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 3;
			res = t.term(t.m_Or, t.term(t.m_Not, params[0]), params[1]);
			break;
		case ProofConstants.SPLIT_POS_ITE_2:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 3;
			res = t.term(t.m_Or, params[0], params[2]);
			break;
		case ProofConstants.SPLIT_NEG_ITE_1:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 3;
			res = t.term(t.m_Or, t.term(t.m_Not, params[0]),
					t.term(t.m_Not, params[1]));
			break;
		case ProofConstants.SPLIT_NEG_ITE_2:
			params = ((ApplicationTerm) data).getParameters();
			assert params.length == 3;
			res = t.term(t.m_Or, params[0], t.term(t.m_Not, params[2]));
			break;
			default:
				throw new InternalError("BUG in ProofTracker: Split");
		}
		return getEqProof(t.term("@split", t.annotatedTerm(
				new Annotation[] {ProofConstants.SPLITANNOTS[splitKind]},
				proof), res));
	}

	@Override
	public Term clause(Term proof) {
		assert(invNumRewrites());
		return getEqProof(proof);
	}

	@Override
	public Term auxAxiom(
			int auxKind, Literal auxLit, Term data, Term base, Object auxData) {
		Theory t = data.getTheory();
		Term axiom;
		switch (auxKind) {
		case ProofConstants.AUX_TRUE_NOT_FALSE:
			// auxLit is (not (= true false)), i.e., it has negative polarity
			axiom = auxLit.getSMTFormula(t, true);
			break;
		case ProofConstants.AUX_OR_POS: {
			Term[] args = ((ApplicationTerm) data).getParameters();
			Term[] nargs = new Term[args.length + 1];
			nargs[0] = t.term(t.m_Not, auxLit.getSMTFormula(t, true));
			System.arraycopy(args, 0, nargs, 1, args.length);
			axiom = t.term(t.m_Or, nargs);
			break;
		}
		case ProofConstants.AUX_OR_NEG:
			axiom = t.term(t.m_Or, auxLit.getSMTFormula(t, true),
						t.term(t.m_Not, data));
			break;
		case ProofConstants.AUX_ITE_POS_1:
			Term[] params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, t.term(t.m_Not, 
					auxLit.getSMTFormula(t, true)),
					t.term(t.m_Not, params[0]), params[1]);
			break;
		case ProofConstants.AUX_ITE_POS_2:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, t.term(t.m_Not,
					auxLit.getSMTFormula(t, true)),
					params[0], params[2]);
			break;
		case ProofConstants.AUX_ITE_POS_RED:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, t.term(t.m_Not,
					auxLit.getSMTFormula(t, true)),
					params[1], params[2]);
			break;
		case ProofConstants.AUX_ITE_NEG_1:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, auxLit.getSMTFormula(t, true),
					t.term(t.m_Not, params[0]), t.term(t.m_Not, params[1]));
			break;
		case ProofConstants.AUX_ITE_NEG_2:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, auxLit.getSMTFormula(t, true),
					params[0], t.term(t.m_Not, params[2]));
			break;
		case ProofConstants.AUX_ITE_NEG_RED:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, auxLit.getSMTFormula(t, true),
					t.term(t.m_Not, params[1]), t.term(t.m_Not, params[2]));
			break;
		case ProofConstants.AUX_EQ_POS_1:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, t.term(t.m_Not,
					auxLit.getSMTFormula(t, true)),
					params[0], t.term(t.m_Not, params[1]));
			break;
		case ProofConstants.AUX_EQ_POS_2:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, t.term(t.m_Not,
					auxLit.getSMTFormula(t, true)),
					t.term(t.m_Not, params[0]), params[1]);
			break;
		case ProofConstants.AUX_EQ_NEG_1:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, auxLit.getSMTFormula(t, true),
					params[0], params[1]);
			break;
		case ProofConstants.AUX_EQ_NEG_2:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, auxLit.getSMTFormula(t, true),
					t.term(t.m_Not, params[0]), t.term(t.m_Not, params[1]));
			break;
		case ProofConstants.AUX_EXCLUDED_MIDDLE_1:
			axiom = t.term(t.m_Or, t.term(t.m_Not, data),
					auxLit.getSMTFormula(t, true));
			break;
		case ProofConstants.AUX_EXCLUDED_MIDDLE_2:
			axiom = t.term(t.m_Or, data, auxLit.getSMTFormula(t, true));
			break;
		case ProofConstants.AUX_TERM_ITE:
			ConditionChain tmp = (ConditionChain) auxData;
			// Determine size
			ConditionChain walk = tmp;
			int size = 1;
			while (walk != null) {
				walk = walk.getPrevious();
				++size;
			}
			Term[] nparams = new Term[size];
			walk = tmp;
			for (int i = size - 2; i >= 0; --i) {
				nparams[i] = t.term(t.m_Not, walk.getTerm());
				if (Utils.isNegation(walk.getTerm()))
					negation(walk.getTerm(),
							Utils.createNotUntracked(walk.getTerm()),
							ProofConstants.RW_NOT_SIMP);
				walk = walk.getPrevious();
			}
			nparams[size - 1] = t.term("=", base, data);
			axiom = t.term(t.m_Or, nparams);
			break;
		case ProofConstants.AUX_DIV_LOW:
			axiom = t.term("<=", SMTAffineTerm.cleanup(data),
					t.numeral(BigInteger.ZERO));
			break;
		case ProofConstants.AUX_TO_INT_LOW:
			axiom = t.term("<=", SMTAffineTerm.cleanup(data),
					t.rational(BigInteger.ZERO, BigInteger.ONE));
			break;
		case ProofConstants.AUX_DIV_HIGH:
			axiom = t.term(t.m_Not, t.term("<=", SMTAffineTerm.cleanup(data),
					t.numeral(BigInteger.ZERO)));
			break;
		case ProofConstants.AUX_TO_INT_HIGH:
			axiom = t.term(t.m_Not, t.term("<=", SMTAffineTerm.cleanup(data),
					t.rational(BigInteger.ZERO, BigInteger.ONE)));
			break;
			default:
				throw new InternalError("BUG in ProofTracker: AUX");
		}
		return t.term("@tautology", t.annotatedTerm(
				new Annotation[] {ProofConstants.AUXANNOTS[auxKind]}, axiom));
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
	public void mod(SMTAffineTerm x, SMTAffineTerm y, SMTAffineTerm res,
			int rule) {
		Theory t = x.getTheory();
		Term mod = t.term(
				"mod", SMTAffineTerm.cleanup(x), SMTAffineTerm.cleanup(y));
		append(new ResultRewrite(mod, SMTAffineTerm.cleanup(res), rule));
	}

	@Override
	public void div(SMTAffineTerm x, SMTAffineTerm y, SMTAffineTerm res,
			int rule) {
		Theory t = x.getTheory();
		Term mod = t.term(
				"div", SMTAffineTerm.cleanup(x), SMTAffineTerm.cleanup(y));
		append(new ResultRewrite(mod, SMTAffineTerm.cleanup(res), rule));
	}

	@Override
	public void toInt(SMTAffineTerm arg, SMTAffineTerm res) {
		Theory t = arg.getTheory();
		Term toint = t.term("to_int", SMTAffineTerm.cleanup(arg));
		append(new ResultRewrite(toint, SMTAffineTerm.cleanup(res),
				ProofConstants.RW_TO_INT));
	}
	
	@Override
	public Term[] prepareIRAHack(Term[] args) {
		return args.clone();
	}

	@Override
	public void negateLit(Literal lit, Theory theory) {
		assert lit.getSign() == -1 : "Literal not negated!";
		Term lhs = theory.term(theory.m_Not,
				SMTAffineTerm.cleanup(lit.getSMTFormula(theory, true)));
		Term rhs = SMTAffineTerm.cleanup(
				lit.getAtom().getSMTFormula(theory, true));
		append(new ResultRewrite(lhs, rhs, ProofConstants.RW_NOT_SIMP));
	}

	@Override
	public void arrayRewrite(Term[] args, Term result, int rule) {
		Theory t = result.getTheory();
		Term input = rule == ProofConstants.RW_STORE_OVER_STORE ?
				t.term("store", args) : t.term("select", args);
		append(new ResultRewrite(input, result, rule));
	}

	private final static class FlattenHelper {
		private Term[] m_Args;
		private int m_Offset;
		public FlattenHelper(Term[] args, int offset) {
			m_Args = args;
			m_Offset = offset;
		}
		public void flatten(
				ArrayDeque<FlattenHelper> todo, ArrayList<Term> args) {
			for (int i = m_Offset; i < m_Args.length; ++i) {
				if (m_Args[i] instanceof ApplicationTerm) {
					ApplicationTerm tst = (ApplicationTerm) m_Args[i];
					if (tst.getFunction() == tst.getTheory().m_Or &&
							tst.tmpCtr <= Config.OCC_INLINE_THRESHOLD) {
						m_Offset = i + 1;
						if (m_Offset < m_Args.length)
							todo.addFirst(this);
						todo.addFirst(new FlattenHelper(tst.getParameters(), 0));
						return;
					}
				}
				args.add(m_Args[i]);
			}
		}
	}
	
	@Override
	public void flatten(Term[] args, boolean simpOr) {
		Theory t = args[0].getTheory();
		ArrayDeque<FlattenHelper> toFlatten =
				new ArrayDeque<FlattenHelper>();
		toFlatten.add(new FlattenHelper(args, 0));
		ArrayList<Term> newArgs = new ArrayList<Term>();
		while (!toFlatten.isEmpty()) {
			FlattenHelper fh = toFlatten.poll();
			fh.flatten(toFlatten, newArgs);
		}
		ApplicationTerm res = (ApplicationTerm) 
				t.term(t.m_Or, newArgs.toArray(new Term[newArgs.size()]));
		if (simpOr)
			orSimpClause(res.getParameters());
		insertAtMarkedPos(
				new ResultRewrite(t.term(t.m_Or, args), res,
						ProofConstants.RW_FLATTEN));
	}
	
	@Override
	public void orSimpClause(Term[] args) {
		Theory t = args[0].getTheory();
		Term[] newArgs = args.clone();
		LinkedHashSet<Term> clause = new LinkedHashSet<Term>();
		for (int i = 0; i < newArgs.length; ++i) {
			Term tmp = SMTAffineTerm.cleanup(newArgs[i]);
			Term newDisj = m_Lits.get(tmp);
			/* This is the case for proxy literals in aux-clauses.  They cannot
			 * merge since otherwise the term would be infinite because the term
			 * would be its own proper subterm.
			 */
			if (newDisj == null)
				newDisj = tmp;
			newArgs[i] = newDisj;
			if (newDisj != t.FALSE)
				clause.add(newDisj);
		}
		Term res;
		if (clause.size() == 0)
			res = t.FALSE;
		else if (clause.size() == 1)
			res = clause.iterator().next();
		else
			res = t.term(t.m_Or, clause.toArray(new Term[clause.size()]));
		Rewrite rw =
				new ResultRewrite(t.term(t.m_Or, newArgs), res,
						ProofConstants.RW_OR_SIMP);
		append(rw);
	}

	@Override
	public void markPosition() {
		m_MarkPos = m_Last;
	}

	@Override
	public Term[] produceAuxAxiom(Literal auxlit, Term... args) {
		Theory t = args[0].getTheory();
		Term[] res = new Term[1 + args.length];
		res[0] = auxlit.getSMTFormula(t, true);
		System.arraycopy(args, 0, res, 1, args.length);
		return res;
	}

	@Override
	public void save() {
		m_Save = m_Last;
		m_SaveNumRewrites = m_NumRewrites;
	}

	@Override
	public void restore() {
		if (m_Save != null) {
			m_Last = m_Save;
			m_Last.m_Next = null;
			m_NumRewrites = m_SaveNumRewrites;
			m_Save = null;
		}
		assert(invNumRewrites());
	}
	
	@Override
	public void cleanSave() {
		m_Save = null;
	}

	@Override
	public void normalized(ConstantTerm term, SMTAffineTerm res) {
		Term rhs = SMTAffineTerm.cleanup(res);
		if (term != rhs)
			append(new ResultRewrite(
					term, rhs, ProofConstants.RW_CANONICAL_SUM));
	}

	@Override
	public boolean notifyLiteral(Literal lit, Term t) {
		return addToLits(SMTAffineTerm.cleanup(t),
				SMTAffineTerm.cleanup(lit.getSMTFormula(t.getTheory(), true)));
	}

	@Override
	public void notifyFalseLiteral(Term t) {
		addToLits(SMTAffineTerm.cleanup(t), t.getTheory().FALSE);
	}

	@Override
	public void storeRewrite(ApplicationTerm store, Term result, boolean arrayFirst) {
		Term array = store.getParameters()[0];
		Term orig = arrayFirst ? store.getTheory().term("=", array, store) :
			store.getTheory().term("=", store, array);
		append(new ResultRewrite(
				orig, result, ProofConstants.RW_STORE_REWRITE));
	}

	@Override
	public void toReal(SMTAffineTerm arg, SMTAffineTerm res) {
		if (res.isConstant()) {
			Term orig = arg.getTheory().term(
					"to_real", SMTAffineTerm.cleanup(arg));
			append(new ResultRewrite(orig, SMTAffineTerm.cleanup(res),
					ProofConstants.RW_TO_REAL));
		}
	}
	
}
