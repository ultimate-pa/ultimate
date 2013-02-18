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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;

/**
 * Build a representation of the formula where only not, or, ite and =/2 are
 * present.  Linear arithmetic terms are converted into SMTAffineTerms.  We
 * normalize quantifiers to universal quantifiers.  Additionally, this term
 * transformer removes all annotations from the formula.
 * @author Jochen Hoenicke, Juergen Christ
 */
public class TermCompiler extends TermTransformer {
	
	private boolean m_By0Seen = false;
	private Map<Term, Set<String>> m_Names;
	
	private IProofTracker m_Tracker;
	private Utils m_Utils;
	private FormulaUnLet m_Unletter = new FormulaUnLet();
	
	public void setProofTracker(IProofTracker tracker) {
		m_Tracker = tracker;
		m_Utils = new Utils(tracker);
	}
	
	public void setAssignmentProduction(boolean on) {
		if (on) {
			m_Names = new HashMap<Term, Set<String>>();
		} else
			m_Names = null;
	}
	
	public Map<Term, Set<String>> getNames() {
		return m_Names;
	}

	public void convert(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol fsym = appTerm.getFunction();
			Term[] params = appTerm.getParameters();
			if (fsym.isLeftAssoc() && params.length > 2) {
				Theory theory = appTerm.getTheory();
				if (fsym == theory.m_And || fsym == theory.m_Or) {
					// We keep n-ary and/or
					enqueueWalker(new BuildApplicationTerm(appTerm));
					pushTerms(params);
					return;
				}
//				m_Tracker.expand(appTerm);
				enqueueWalker(new RewriteAdder(appTerm, null));
				BuildApplicationTerm dummy = new BuildApplicationTerm
						(theory.term(fsym, params[0], params[1]));
				for (int i = params.length-1; i > 0; i--) {
					enqueueWalker(dummy);
					pushTerm(params[i]);
				}
				pushTerm(params[0]);
				return;
			}
			if (fsym.isRightAssoc() && params.length > 2) {
				Theory theory = appTerm.getTheory();
				if (fsym == theory.m_Implies) {
					// We keep n-ary implies
					enqueueWalker(new BuildApplicationTerm(appTerm));
					pushTerms(params);
					return;
				}
//				m_Tracker.expand(appTerm);
				enqueueWalker(new RewriteAdder(appTerm, null));
				BuildApplicationTerm dummy = new BuildApplicationTerm
					(theory.term(fsym, params[params.length-2], 
							params[params.length-1]));
				for (int i = params.length-1; i > 0; i--)
					enqueueWalker(dummy);
				pushTerms(params);
				return;
			}
			if (fsym.isChainable() && params.length > 2 && 
					!fsym.getName().equals("=")) {
//				m_Tracker.expand(appTerm);
				enqueueWalker(new RewriteAdder(appTerm, null));
				Theory theory = appTerm.getTheory();
				BuildApplicationTerm and = new BuildApplicationTerm
						(theory.term("and", theory.TRUE, theory.TRUE));
				BuildApplicationTerm dummy = new BuildApplicationTerm
						(theory.term(fsym, params[0], params[1]));
				for (int i = params.length-1; i > 1; i--) {
					enqueueWalker(and);
					enqueueWalker(dummy);
					pushTerm(params[i]);
					pushTerm(params[i-1]);
				}
				enqueueWalker(dummy);
				pushTerm(params[1]);
				pushTerm(params[0]);
				return;
			}
		} else if (term instanceof ConstantTerm) {
			setResult(SMTAffineTerm.create(term));
			return;
		} else if (term instanceof AnnotatedTerm)
			m_Tracker.strip((AnnotatedTerm) term);
		super.convert(term);
	}
	
	/**
	 * Add the rewrite that expands a function definition to the beginning
	 * of the rewrite list.  Since this definition must come before the 
	 * definition used inside, we use a Walker to add the definition after
	 * we transformed the expanded term.
	 */
	private static class RewriteAdder implements Walker {
		private ApplicationTerm m_AppTerm;
		private Term m_Expanded;
		
		public RewriteAdder(ApplicationTerm term, Term expanded) {
			m_AppTerm = term;
			m_Expanded = expanded;
		}
		
		public void walk(NonRecursive engine) {
			TermCompiler transformer = (TermCompiler) engine;
			if (m_Expanded == null)
				transformer.m_Tracker.expand(m_AppTerm);
			else
				transformer.m_Tracker.expandDef(m_AppTerm, m_Expanded);
		}

		public String toString() {
			return "addrewrite " + m_AppTerm.getFunction().getApplicationString();
		}
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] args) {
		FunctionSymbol fsym = appTerm.getFunction();
		Theory theory = appTerm.getTheory();
		
 		if (fsym.getDefinition() != null) {
			Term definition = theory.let(
					fsym.getDefinitionVars(), appTerm.getParameters(), 
					fsym.getDefinition());
			Term expanded = m_Unletter.unlet(definition);
			enqueueWalker(new RewriteAdder(appTerm, expanded));
			pushTerm(expanded);
			return;
		} 
		
		boolean iraHackApplied = false;
		if (theory.getLogic().isIRA()
			&& fsym.getParameterCount() == 2 
			&& fsym.getParameterSort(0).getName().equals("Real") 
			&& fsym.getParameterSort(1) == fsym.getParameterSort(0)) {
			// IRA-Hack
			if (args == appTerm.getParameters())
				args = args.clone();
			for (int i = 0; i < args.length; i++) {
				if (args[i].getSort().getName().equals("Int")) {
					args[i] = SMTAffineTerm.create(args[i])
						.toReal(fsym.getParameterSort(0));
					iraHackApplied = true;
				}
			}
		}
		if (iraHackApplied)
			m_Tracker.desugar(appTerm, args);
		
		boolean hasAffineArgs = false;
		for (int i = 0; i < args.length; ++i) {
			if (args[i] instanceof SMTAffineTerm) {
				args[i] = ((SMTAffineTerm) args[i]).normalize();
				hasAffineArgs = true;
			}
		}
		
		if (fsym.isIntern()) {
			if (fsym == theory.m_Not) {
				setResult(m_Utils.createNot(args[0]));
				return;
			}
			if (fsym == theory.m_And) {
				setResult(m_Utils.createAnd(args));
				return;
			}
			if (fsym == theory.m_Or) {
				setResult(m_Utils.createOr(args));
				return;
			}
			if (fsym == theory.m_Xor) {
				m_Tracker.removeConnective(args,
						null, ProofConstants.RW_XOR_TO_DISTINCT);
				setResult(m_Utils.createDistinct(args));
				return;
			}
			if (fsym == theory.m_Implies) {
				m_Tracker.removeConnective(
						args, null, ProofConstants.RW_IMP_TO_OR);
				Term[] tmp = new Term[args.length];
				// We move the conclusion in front (see Simplify tech report)
				for (int i = 1; i < args.length; ++i)
					tmp[i] = m_Utils.createNot(args[i - 1]);
				tmp[0] = args[args.length - 1];
				setResult(m_Utils.createOr(tmp));
				return;
			}
			if (fsym.getName().equals("ite")) {
				setResult(m_Utils.createIte(args[0], args[1], args[2]));
				return;
			}
			if (fsym.getName().equals("=")) {
				setResult(m_Utils.createEq(args));
				return;
			}
			if (fsym.getName().equals("distinct")) {
				setResult(m_Utils.createDistinct(args));
				return;
			}
			if (fsym.getName().equals("<=")) {
				SMTAffineTerm res = SMTAffineTerm.create(args[0])
						.add(SMTAffineTerm.create(Rational.MONE, args[1]));
				m_Tracker.removeConnective(
						args, res, ProofConstants.RW_LEQ_TO_LEQ0);
				setResult(m_Utils.createLeq0(res));
				return;
			}
			if (fsym.getName().equals(">=")) {
				SMTAffineTerm res = SMTAffineTerm.create(args[1])
						.add(SMTAffineTerm.create(Rational.MONE, args[0]));
				m_Tracker.removeConnective(
						args, res, ProofConstants.RW_GEQ_TO_LEQ0);
				setResult(m_Utils.createLeq0(res));
				return;
			}
			if (fsym.getName().equals(">")) {
				SMTAffineTerm res = SMTAffineTerm.create(args[0])
						.add(SMTAffineTerm.create(Rational.MONE, args[1]));
				m_Tracker.removeConnective(
						args, res, ProofConstants.RW_GT_TO_LEQ0);
				setResult(m_Utils.createNot(m_Utils.createLeq0(res)));
				return;
			}
			if (fsym.getName().equals("<")) {
				SMTAffineTerm res = SMTAffineTerm.create(args[1])
						.add(SMTAffineTerm.create(Rational.MONE, args[0]));
				m_Tracker.removeConnective(
						args, res, ProofConstants.RW_LT_TO_LEQ0);
				setResult(m_Utils.createNot(m_Utils.createLeq0(res)));
				return;
			}
			if (fsym.getName().equals("+")) {
				setResult(SMTAffineTerm.create(args[0])
						.add(SMTAffineTerm.create(args[1])));
				return;
			}
			else if (fsym.getName().equals("-") && fsym.getParameterCount() == 2) {
				setResult(SMTAffineTerm.create(args[0])
						.add(SMTAffineTerm.create(Rational.MONE, args[1])));
				return;
			} 
			else if (fsym.getName().equals("*")) {
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(args[1]);
				if (arg0.isConstant()) {
					setResult(arg1.mul(arg0.getConstant()));
					return;
				} else if (arg1.isConstant()) {
					setResult(arg0.mul(arg1.getConstant()));
					return;
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (fsym.getName().equals("/")) {
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(args[1]);
				if (arg1.isConstant()) {
					if (arg1.getConstant().equals(Rational.ZERO)) {
						m_By0Seen = true;
						setResult(theory.term("@/0", arg0));
					} else
						setResult(arg0.mul(arg1.getConstant().inverse()));
					return;
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (fsym.getName().equals("div") && fsym.getParameterCount() == 2) {
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(args[1]);
				Rational divisor = arg1.getConstant();
				if (arg1.isConstant() && divisor.isIntegral()) {
				    if (divisor.equals(Rational.ZERO)) {
				    	m_By0Seen = true;
				    	setResult(theory.term("@div0", arg0));
				    } else if (divisor.equals(Rational.ONE)) {
				    	m_Tracker.div(arg0, arg1, arg0,
				    			ProofConstants.RW_DIV_ONE);
				    	setResult(arg0);
				    } else if (divisor.equals(Rational.MONE)) {
				    	SMTAffineTerm res = arg0.negate();
				    	m_Tracker.div(arg0, arg1, res,
				    			ProofConstants.RW_DIV_MONE);
				    	setResult(res);
				    } else if (arg0.isConstant()) {
				    	// We have (div c0 c1) ==> constDiv(c0, c1)
				    	Rational div = constDiv(arg0.getConstant(),
				    			arg1.getConstant());
				    	SMTAffineTerm res = SMTAffineTerm.create(
				    			theory.constant(div, arg0.getSort()));
				    	m_Tracker.div(arg0, arg1, res,
				    			ProofConstants.RW_DIV_CONST);
				    	setResult(res);
				    } else {
				    	setResult(arg0.getTheory().term(fsym, arg0, arg1));
				    }
					return;
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (fsym.getName().equals("mod")) {
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(args[1]);
				Rational divisor = arg1.getConstant();
				if (arg1.isConstant() && divisor.isIntegral()) {
				    if (divisor.equals(Rational.ZERO)) {
				    	m_By0Seen = true;
				    	setResult(theory.term("@mod0", arg0));
				    } else if (divisor.equals(Rational.ONE)) {
				    	// (mod x 1) == 0
				    	SMTAffineTerm res = SMTAffineTerm.create(
				    			theory.constant(Rational.ZERO, arg0.getSort()));
				    	m_Tracker.mod(arg0, arg1, res,
				    			ProofConstants.RW_MODULO_ONE);
				    	setResult(res);
				    } else if (divisor.equals(Rational.MONE)) {
				    	// (mod x -1) == 0
				    	SMTAffineTerm res = SMTAffineTerm.create(
				    			theory.constant(Rational.ZERO, arg0.getSort()));
				    	m_Tracker.mod(arg0, arg1, res,
				    			ProofConstants.RW_MODULO_MONE);
				    	setResult(res);
				    } else if (arg0.isConstant()) {
				    	// We have (mod c0 c1) ==> c0 - c1 * constDiv(c0, c1)
				    	Rational c0 = arg0.getConstant();
				    	Rational c1 = arg1.getConstant();
				    	Rational mod = c0.sub(constDiv(c0, c1).mul(c1));
				    	SMTAffineTerm res = SMTAffineTerm.create(
				    			theory.constant(mod, arg0.getSort()));
				    	m_Tracker.mod(arg0, arg1, res,
				    			ProofConstants.RW_MODULO_ONE);
				    	setResult(res);
				    } else {
				    	Theory t = arg0.getTheory();
				    	SMTAffineTerm ydiv =
				    			SMTAffineTerm.create(t.term("div", arg0, arg1)).
				    			mul(arg1.getConstant());
				    	Term res = arg0.add(ydiv.negate());
				    	setResult(res);
				    	m_Tracker.modulo(appTerm, res);
				    }
					return;
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (fsym.getName().equals("-") && fsym.getParameterCount() == 1) {
				setResult(SMTAffineTerm.create(args[0]).negate());
				return;
			} else if (fsym.getName().equals("to_real") && fsym.getParameterCount() == 1) {
				setResult(SMTAffineTerm.create(args[0]).toReal(fsym.getReturnSort()));
				return;
			} else if (fsym.getName().equals("to_int") && fsym.getParameterCount() == 1) {
				// We don't convert to_int here but defer it to the clausifier
				// But we simplify it here...
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				if (arg0.isConstant()) {
					SMTAffineTerm res = SMTAffineTerm.create(
							arg0.getConstant().floor().toTerm(arg0.getSort()));
					m_Tracker.toInt(arg0, res);
					setResult(res);
					return;
				}
			}  else if (fsym.getName().equals("divisible")) {
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(
						Rational.valueOf(fsym.getIndices()[0], BigInteger.ONE),
						arg0.getSort());
				Term res = theory.term("=", arg0,
						theory.term("*", arg1,
								theory.term("div", arg0, arg1)));
				setResult(res);
				m_Tracker.divisible(appTerm, res);
				return;
			}
		} else if (hasAffineArgs)
			m_Tracker.trackSums(appTerm.getParameters(), args);
		super.convertApplicationTerm(appTerm, args);
	}
	
	public final static Rational constDiv(Rational c0, Rational c1) {
		Rational div = c0.div(c1);
		return c1.isNegative() ? div.ceil() : div.floor();
	}

	@Override
	public void postConvertQuantifier(QuantifiedFormula old, Term newBody) {
		if (old.getQuantifier() == QuantifiedFormula.EXISTS)
			super.postConvertQuantifier(old, newBody);
		else {
			// We should create (forall (x) (newBody x))
			// This becomes (not (exists (x) (not (newBody x))))
			Term negNewBody = m_Utils.createNot(newBody);
			Theory t = old.getTheory();
			Term res = t.term(t.m_Not,
					t.exists(old.getVariables(), negNewBody));
			setResult(res);
		}
	}

	@Override
	public void postConvertAnnotation(AnnotatedTerm old,
			Annotation[] newAnnots, Term newBody) {
		if (m_Names != null &&
				newBody.getSort() == newBody.getTheory().getBooleanSort()) {
			Annotation[] oldAnnots = old.getAnnotations();
			for (Annotation annot : oldAnnots) {
				if (annot.getKey().equals(":named")) {
					Set<String> oldNames = m_Names.get(newBody);
					if (oldNames == null) {
						oldNames = new HashSet<String>();
						m_Names.put(newBody, oldNames);
					}
					oldNames.add(annot.getValue().toString());
				}
			}
		}
		setResult(newBody);
	}
	/**
	 * Get and reset the division-by-0 seen flag.
	 * @return The old division-by-0 seen flag.
	 */
	public boolean resetBy0Seen() {
		boolean old = m_By0Seen;
		m_By0Seen = false;
		return old;
	}
}
