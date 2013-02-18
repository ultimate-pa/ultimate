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

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
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
			m_Old = oldTerm;
			m_New = newTerm;
			m_Num = rewriteNum;
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
	
	private Rewrite m_First, m_Last;
	private int m_NumRewrites = 0;

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
	
	private boolean invNumRewrites() {
		int i = 0;
		for (Rewrite rw = m_First.m_Next; rw != null; rw = rw.m_Next)
			++i;
		assert (i == m_NumRewrites);
		return i == m_NumRewrites;
	}
	
	public ProofTracker() {
		m_First = m_Last = new Rewrite();
	}

	@Override
	public void reset() {
		m_First.m_Next = null;
		m_Last = m_First;
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
			if (rule == ProofConstants.RW_EQ_TRUE) {
				tres = t.term(t.m_And, (Term[]) res);
			} else if (rule == ProofConstants.RW_EQ_FALSE) {
				tres = t.term(t.m_Not, t.term(t.m_Or, (Term[]) res));
			} else if (rule == ProofConstants.RW_EQ_SIMP) {
				tres = t.term("=", (Term[]) res);
			} else
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
				t.term(t.m_Not,	t.term(t.m_Or, t.term(t.m_Not, cond),
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
		append(new ResultRewrite(
				orig, orig.getSubterm(), ProofConstants.RW_STRIP));
	}

	@Override
	public void sum(Term orig, Term res) {
		Term left = SMTAffineTerm.cleanup(orig);
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
	public void desugar(ApplicationTerm orig, Term[] newArgs) {
		append(new ResultRewrite(orig,
				orig.getTheory().term(orig.getFunction(), newArgs),
				ProofConstants.RW_DESUGAR));
	}

	@Override
	public void divisible(Term div, Term res) {
		append(new ResultRewrite(div, res, ProofConstants.RW_DIVISIBLE));
	}

	@Override
	public Term getRewriteProof(Term asserted, Term result) {
		assert(invNumRewrites());
		Theory t = asserted.getTheory();
		if (m_NumRewrites == 0)
			// No @eq proof if no rewrites
			return t.term("@asserted", asserted);
		Term[] args = new Term[m_NumRewrites + 1];
		args[0] = t.term("@asserted", asserted);
		int i = 1;
		for (Rewrite rw = m_First.m_Next; rw != null; rw = rw.m_Next)
			args[i++] = rw.toTerm();
		Term eq = t.term("@eq", args);
//		if (m_NumRewrites == 1 && m_First.m_Next.isTarget(asserted))
			return eq;
//		return t.term("@result", eq, result);
	}

	@Override
	public void trackSums(Term[] origArgs, Term[] newArgs) {
		assert origArgs.length == newArgs.length : 
			"Different number of arguments?";
		for (int i = 0; i < origArgs.length; ++i) {
			if (newArgs[i] instanceof SMTAffineTerm)
				sum(origArgs[i], newArgs[i]);
		}
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
		append(new RemoveConnective(rule, origArgs, result));
	}

	@Override
	public void quoted(Term orig, Literal quote) {
		append(new InternRewrite(orig,
				quote.getSMTFormula(orig.getTheory(), true)));
	}

	@Override
	public void eq(Term lhs, Term rhs, Term res) {
		Term orig = res.getTheory().term("=", lhs, rhs);
		if (orig != res)
			append(new InternRewrite(orig, res));
	}

	@Override
	public void eq(Term lhs, Term rhs, DPLLAtom eqAtom) {
		Theory t = lhs.getTheory();
		Term res = eqAtom.getSMTFormula(t);
		Term orig = t.term("=", lhs, rhs);
		if (orig != res)
			append(new InternRewrite(orig, res));
	}

	@Override
	public void leq0(SMTAffineTerm sum, Literal lit) {
		Theory t = sum.getTheory();
		Term orig = t.term("<=", SMTAffineTerm.cleanup(sum),
				sum.getSort().getName().equals("Int") ?
						t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO));
		Term res = lit.getSMTFormula(t);
		if (orig != res)
			append(new InternRewrite(orig, res));
	}

	@Override
	public void intern(Term term, Literal lit) {
		Theory t = term.getTheory();
		Term orig = SMTAffineTerm.cleanup(term);
		Term res = lit.getSMTFormula(t);
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
			if (Utils.isNegation(data)) {
				Term posRes = ((ApplicationTerm) data).getParameters()[0];
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
		return t.term("@split", t.annotatedTerm(
				new Annotation[] {ProofConstants.SPLITANNOTS[splitKind]},
				proof), res);
	}

	@Override
	public Term clause(Term proof) {
		assert(invNumRewrites());
		Theory t = proof.getTheory();
		if (m_NumRewrites != 0) {
			// First do the rewrites
			Term[] args = new Term[m_NumRewrites + 1];
			args[0] = proof;
			int i = 1;
			for (Rewrite rw = m_First.m_Next; rw != null; rw = rw.m_Next)
				args[i++] = rw.toTerm();
			proof = t.term("@eq", args);
		}
		return proof;
	}

	@Override
	public Term auxAxiom(int auxKind, Literal auxLit, Term data, Term base, Object auxData) {
		Theory t = data.getTheory();
		Term axiom;
		switch (auxKind) {
		case ProofConstants.AUX_TRUE_NOT_FALSE:
			axiom = t.term(t.m_Not, t.term("=", t.TRUE, t.FALSE));
			break;
		case ProofConstants.AUX_OR_POS:
			axiom = t.term(t.m_Or, t.term(t.m_Not, auxLit.getSMTFormula(t)),
					data);
			break;
		case ProofConstants.AUX_OR_NEG:
			axiom = t.term(t.m_Or, auxLit.getSMTFormula(t),
						t.term(t.m_Not, data));
			break;
		case ProofConstants.AUX_ITE_POS_1:
			Term[] params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, t.term(t.m_Not, auxLit.getSMTFormula(t)),
					t.term(t.m_Not, params[0]), params[1]);
			break;
		case ProofConstants.AUX_ITE_POS_2:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, t.term(t.m_Not, auxLit.getSMTFormula(t)),
					params[0], params[2]);
			break;
		case ProofConstants.AUX_ITE_POS_RED:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, t.term(t.m_Not, auxLit.getSMTFormula(t)),
					params[1], params[2]);
			break;
		case ProofConstants.AUX_ITE_NEG_1:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, auxLit.getSMTFormula(t),
					t.term(t.m_Not, params[0]), t.term(t.m_Not, params[1]));
			break;
		case ProofConstants.AUX_ITE_NEG_2:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, auxLit.getSMTFormula(t),
					params[0], t.term(t.m_Not, params[2]));
			break;
		case ProofConstants.AUX_ITE_NEG_RED:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, auxLit.getSMTFormula(t),
					t.term(t.m_Not, params[1]), t.term(t.m_Not, params[2]));
			break;
		case ProofConstants.AUX_EQ_POS_1:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, t.term(t.m_Not, auxLit.getSMTFormula(t)),
					params[0], t.term(t.m_Not, params[1]));
			break;
		case ProofConstants.AUX_EQ_POS_2:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, t.term(t.m_Not, auxLit.getSMTFormula(t)),
					t.term(t.m_Not, params[0]), params[1]);
			break;
		case ProofConstants.AUX_EQ_NEG_1:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, auxLit.getSMTFormula(t),
					params[0], params[1]);
			break;
		case ProofConstants.AUX_EQ_NEG_2:
			params = ((ApplicationTerm) data).getParameters();
			axiom = t.term(t.m_Or, auxLit.getSMTFormula(t),
					t.term(t.m_Not, params[0]), t.term(t.m_Not, params[1]));
			break;
		case ProofConstants.AUX_EXCLUDED_MIDDLE_1:
			// Fall through since they only differ in the literal. 
		case ProofConstants.AUX_EXCLUDED_MIDDLE_2:
			axiom = t.term(t.m_Or, data, auxLit.getSMTFormula(t));
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
				nparams[i] = walk.getTerm();
				walk = walk.getPrevious();
			}
			nparams[size - 1] = t.term("=", base, data);
			axiom = t.term(t.m_Or, nparams);
			break;
		case ProofConstants.AUX_DIV_LOW:
		case ProofConstants.AUX_TO_INT_LOW:
			axiom = t.term("<=", SMTAffineTerm.cleanup(data),
					t.numeral(BigInteger.ZERO));
			break;
		case ProofConstants.AUX_DIV_HIGH:
		case ProofConstants.AUX_TO_INT_HIGH:
			axiom = t.term(t.m_Not, t.term("<=", SMTAffineTerm.cleanup(data),
					t.numeral(BigInteger.ZERO)));
			break;
			default:
				throw new InternalError("BUG in ProofTracker: AUX");
		}
		return t.term("@tautology", t.annotatedTerm(new Annotation[] {
				ProofConstants.AUXANNOTS[auxKind]}, axiom));
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

}
