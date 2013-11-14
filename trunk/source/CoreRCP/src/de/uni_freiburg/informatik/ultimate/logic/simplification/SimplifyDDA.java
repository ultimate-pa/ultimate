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
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Simplify formulas, but keep their Boolean structure.
 * Replace subformulas by true or false if this replacement leads to an
 * equivalent formula.
 * Based on the paper "Small Formulas for Large Programms: On-Line Constraint
 * Simplification in Scalable Static Analysis" by Isil Dillig, Thomas Dillig
 * and Alex Aiken.
 * This implementation extends this approach to formulas which are not in NNF,
 * contain "=>" and "ite".
 * 
 * The new implementation is DAG-based an non-recursive.  We collect contexts
 * 
 * @author Matthias Heizmann, Jochen Hoenicke, Markus Pomrehn
 *
 */
public class SimplifyDDA extends NonRecursive {

	private static class TermInfo {
		int    m_numPredecessors;
		int    m_seen;
		int    m_prepared;
		Term[] m_context;
		Term   m_simplified;
		
		public String toString() {
			return "TermInfo["+m_numPredecessors+","+m_seen+","+m_prepared
			+(m_context != null ? ",context:"+Arrays.toString(m_context): "")
			+(m_simplified != null ? "->"+m_simplified : "")+"]";
		}
	}
	
	HashMap<Term, TermInfo> m_termInfos; 
	Term m_Result;
	Script m_Script;
	Term m_True;
	Term m_False;
	boolean m_SimplifyRepeatedly;

	/**
	 * This class counts the predecessors of every term to enable the
	 * next passes to determine whether we need to collect information.
	 * 
	 * @author hoenicke
	 */
	private static class TermCounter implements Walker {
		protected Term m_Term;
		public TermCounter(Term term) {
			/* directly descend into not-terms as if the not is not there */
			while (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName() == "not")
					term = appTerm.getParameters()[0];
				else
					break;
			}
			m_Term = term;
		}

		@Override
		public void walk(NonRecursive engine) {
			SimplifyDDA simplifier = (SimplifyDDA) engine;
			TermInfo info = simplifier.m_termInfos.get(m_Term);
			if (info == null) {
				info = new TermInfo();
				simplifier.m_termInfos.put(m_Term, info);

				if (m_Term instanceof ApplicationTerm) {
					ApplicationTerm appTerm = (ApplicationTerm) m_Term;
					String connective = appTerm.getFunction().getName();
					
					if (connective == "ite" || connective == "and" || 
						connective == "or" || connective == "=>") {
						for (Term subTerm : appTerm.getParameters()) {
							engine.enqueueWalker(new TermCounter(subTerm));
						}
					}
				}
			}
			info.m_numPredecessors++;
		}
	}
	
	/**
	 * This class collects the contexts (for the context simplifier)
	 * in which a term occurs.  It does not simplify the term.
	 * 
	 * @author hoenicke
	 */
	private static class ContextCollector implements Walker {
		boolean m_negated;
		Term m_term;
		ArrayDeque<Term> m_context;
		int m_paramCtr;
		
		public ContextCollector(boolean negated, Term term, 
				                ArrayDeque<Term> context) {
			/* directly descend into not-terms as if the not is not there */
			while (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName() == "not") {
					term = appTerm.getParameters()[0];
					negated = !negated;
				} else
					break;
			}
			m_negated = negated;
			m_term = term;
			m_context = context;
			m_paramCtr = 0;
		}

		@Override
		public void walk(NonRecursive engine) {
			SimplifyDDA simplifier = (SimplifyDDA) engine;
			if (m_paramCtr > 0) {
				walkNextParameter(simplifier);
				return;
			}
			TermInfo info = simplifier.m_termInfos.get(m_term);
			assert info != null;
			info.m_seen++;
			assert info.m_seen <= info.m_numPredecessors;
			if (info.m_numPredecessors > 1) {
				// merge context
				if (info.m_context == null) {
					info.m_context = m_context.toArray(new Term[m_context.size()]);
				} else {
					HashSet<Term> oldContext = new HashSet<Term>(info.m_context.length);
					oldContext.addAll(Arrays.asList(info.m_context));
					ArrayList<Term> newContext = new ArrayList<Term>(info.m_context.length);
					for (Term t : m_context) {
						if (oldContext.contains(t))
							newContext.add(t);
					}
					info.m_context = newContext.toArray(new Term[newContext.size()]);
				}
				if (info.m_seen < info.m_numPredecessors)
					return;
			}
		
			if (m_term instanceof ApplicationTerm) {
				walkNextParameter(simplifier);
			}
		}

		public void walkNextParameter(SimplifyDDA simplifier) {
			ApplicationTerm appTerm = (ApplicationTerm) m_term;
			String connective = appTerm.getFunction().getName();
			Term[] params = appTerm.getParameters();
				
			if (connective == "ite") {
				Term cond = params[0];
				if (m_paramCtr == 0) {
					simplifier.enqueueWalker(this);
					simplifier.enqueueWalker(new ContextCollector(false, cond, m_context));
				} else if (m_paramCtr == 1) {
					m_context.push(cond);
					simplifier.enqueueWalker(this);
					simplifier.enqueueWalker(new ContextCollector(m_negated, params[1], m_context));
				} else if (m_paramCtr == 2) {
					m_context.pop();
					m_context.push(Util.not(simplifier.m_Script, cond));
					simplifier.enqueueWalker(this);
					simplifier.enqueueWalker(new ContextCollector(m_negated, params[2], m_context));
				} else if (m_paramCtr == 3) {
					m_context.pop();
				}
				m_paramCtr++;
			} else if (connective == "and" || 
					   connective == "or" || connective == "=>") {
				if (m_paramCtr == 0) {
					for (int i = params.length-1; i > 0; i--) {
						Term sibling = simplifier.negateSibling(params[i], connective, i, params.length);
						m_context.push(sibling);
					}
					simplifier.enqueueWalker(this);
					simplifier.enqueueWalker(new ContextCollector(m_negated, params[m_paramCtr], m_context));
				} else if (m_paramCtr < params.length) {
					// The context contains:
					//  param[len-1] ... param[m_paramCtr] 
					//      simplify(param[m_paramCtr-2])... simplify(param[0])
					// we need to replace param[m_paramCtr]
					// by simplify(param[m_paramCtr-1]).
					/*  this is dangerous:  the simplified formulas may depend
					 * on their context, therefore we cannot simply merge them.
					for (int i = 0; i < m_paramCtr; i++) {
						m_context.pop();
					}
					for (int i = m_paramCtr-1; i >= 0; i--) {
						Term sibling = simplifier.negateSibling(params[i], connective, i, params.length);
						sibling = simplifier.createSimplify(sibling);
						m_context.push(sibling);
					}
					*/
					m_context.pop();
					simplifier.enqueueWalker(this);
					simplifier.enqueueWalker(new ContextCollector(m_negated, params[m_paramCtr], m_context));
				} else {
					/*
					for (int i = 0; i < m_paramCtr-1; i++) {
						m_context.pop();
					}
					*/
				}
				m_paramCtr++;
			}
		}
	}

	/**
	 * This class simplifies the terms in a post-order traversal.  First we
	 * descend into children doing nothing.  When getting back to the parent
	 * again we simplify it, provided it has more than one predecessor.
	 * 
	 * @author hoenicke
	 */
	private static class PrepareSimplifier implements Walker {
		Term m_term;
		
		public PrepareSimplifier(boolean negated, Term term) {
			/* directly descend into not-terms as if the not is not there */
			while (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName() == "not") {
					term = appTerm.getParameters()[0];
				} else
					break;
			}
			m_term = term;
		}

		@Override
		public void walk(NonRecursive engine) {
			SimplifyDDA simplifier = (SimplifyDDA) engine;
			TermInfo info = simplifier.m_termInfos.get(m_term);
			if (info.m_prepared++ > 0)
				return;
			
			if (info.m_numPredecessors > 1) {
				engine.enqueueWalker(new StoreSimplified(m_term));
				engine.enqueueWalker(new Simplifier(false, m_term, info.m_context));
			}
			if (m_term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) m_term;
				String connective = appTerm.getFunction().getName();
				Term[] params = appTerm.getParameters();
			
				if (connective == "ite" || connective == "and" || 
					connective == "or" || connective == "=>") {
					for (int i = 0; i < params.length; i++)
						engine.enqueueWalker(new PrepareSimplifier(false, params[i]));
				}
			}
		}
	}
	
	private static class StoreSimplified implements Walker {
		Term m_term;
		
		public StoreSimplified(Term term) {
			m_term = term;
		}

		@Override
		public void walk(NonRecursive engine) {
			SimplifyDDA simplifier = (SimplifyDDA) engine;
			TermInfo info = simplifier.m_termInfos.get(m_term);
			info.m_simplified = simplifier.popResult();
		}
	}

	private static class Simplifier implements Walker {
		boolean m_negated;
		Term m_term;
		Term[] m_context;
		int m_paramCtr;
		Term[] m_simplifiedParams;
		
		public Simplifier(boolean negated, Term term, Term[] context) {
			/* directly descend into not-terms as if the not is not there */
			while (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName() == "not") {
					term = appTerm.getParameters()[0];
					negated = !negated;
				} else
					break;
			}
			m_negated = negated;
			m_term = term;
			m_context = context;
			m_paramCtr = 0;
		}

		public Simplifier(boolean negated, Term term) {
			/* directly descend into not-terms as if the not is not there */
			while (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName() == "not") {
					term = appTerm.getParameters()[0];
					negated = !negated;
				} else
					break;
			}
			m_negated = negated;
			m_term = term;
			m_context = null;
			m_paramCtr = 0;
		}

		@Override
		public void walk(NonRecursive engine) {		
			SimplifyDDA simplifier = (SimplifyDDA) engine;
			if (m_paramCtr > 0) {
				walkParam(simplifier);
				return;
			}
			if (m_context == null) {
				/* check for redundancy, then for info */
				Redundancy red = simplifier.getRedundancy(m_term);
				if (red != Redundancy.NOT_REDUNDANT) {
					if (red == Redundancy.NON_RELAXING)
						simplifier.setResult(m_negated, simplifier.m_False);
					else
						simplifier.setResult(m_negated, simplifier.m_True);
					return;
				}
				
				TermInfo info = simplifier.m_termInfos.get(m_term);
				if (info.m_numPredecessors > 1) {
					assert info.m_simplified != null;
					simplifier.setResult(m_negated, info.m_simplified);
					return;
				}
			}
			
			if (m_context != null)
				simplifier.pushContext(m_context);

			if (m_term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) m_term;
				String connective = appTerm.getFunction().getName();
				Term[] params = appTerm.getParameters();

				if (connective == "ite" || connective == "and" || 
					connective == "or" || connective == "=>") {
					m_simplifiedParams = new Term[params.length];
					walkParam(simplifier);
					return;
				}
			}
			/* we could not simplify this term */
			simplifier.setResult(m_negated, m_term);
			if (m_context != null)
				simplifier.popContext();
		}

		private void walkParam(SimplifyDDA simplifier) {
			ApplicationTerm appTerm = (ApplicationTerm) m_term;
			String connective = appTerm.getFunction().getName();
			Term[] params = appTerm.getParameters();

			if (m_paramCtr > 0)
				m_simplifiedParams[m_paramCtr-1] = simplifier.popResult();

			if (connective == "ite") {
				switch (m_paramCtr++) {
				case 0:
					simplifier.enqueueWalker(this);
					simplifier.enqueueWalker(new Simplifier(false, params[0]));
					break;
				case 1:
					simplifier.enqueueWalker(this);
					simplifier.pushContext(m_simplifiedParams[0]);
					simplifier.enqueueWalker(new Simplifier(m_negated, params[1]));
					break;
				case 2:
					simplifier.enqueueWalker(this);
					simplifier.popContext();
					simplifier.pushContext(Util.not(simplifier.m_Script, m_simplifiedParams[0]));
					simplifier.enqueueWalker(new Simplifier(m_negated, params[2]));
					break;
				case 3:
					simplifier.popContext();
					Term result = Util.ite(simplifier.m_Script, 
							m_simplifiedParams[0], m_simplifiedParams[1], m_simplifiedParams[2]);
					simplifier.setResult(false, result);
					if (m_context != null)
						simplifier.popContext();
					break;
				}
			} else {
				assert (connective == "and" || connective == "or" 
					|| connective == "=>");
				if (m_paramCtr == params.length) {
					simplifier.popContext();
					ArrayList<Term> newparams = new ArrayList<Term>();
					Term result = null;
					for (int i = 0; i < m_simplifiedParams.length; i++) {
						Term param = m_simplifiedParams[i];
						if (param == simplifier.m_True) {
							if (connective == "and" || 
								(connective == "=>" && i < m_simplifiedParams.length - 1))
								continue;
							if (connective == "or" ||
								(connective == "=>" && i == m_simplifiedParams.length - 1)) {
								result = simplifier.m_True;
								break;
							}
						} else if (param == simplifier.m_False) {
							if (connective == "or")
								continue;
							if (connective == "and") {
								result = simplifier.m_False;
								break;
							}
							if (connective == "=>" && i < m_simplifiedParams.length - 1) {
								result = simplifier.m_True;
								break;
							}
						}
						newparams.add(param);
					}
					if (result == null) {
						if (newparams.isEmpty()) {
							result = connective == "and" ? simplifier.m_True  
									: simplifier.m_False;
						} else if (newparams.size() == 1) {
							result = newparams.get(0);
						} else {
							Term[] p = newparams.toArray(new Term[newparams.size()]);
							result = simplifier.m_Script.term(connective, p);
						}
					}
					simplifier.setResult(m_negated, result);
					if (m_context != null)
						simplifier.popContext();
					return;
				}
				if (m_paramCtr == 0) {
					simplifier.pushContext();
					for (int i = params.length-1; i >= 1; i--) {
						Term sibling = simplifier.negateSibling(params[i], connective, i, params.length);
						simplifier.pushContext(sibling);
					}
				} else {
					simplifier.popContext();
					for (int i = 0; i < m_paramCtr; i++) {
						Term sibling = simplifier.negateSibling(m_simplifiedParams[i], connective, i, params.length);
						simplifier.m_Script.assertTerm(sibling);
					}
				}
				simplifier.enqueueWalker(this);
				simplifier.enqueueWalker(new Simplifier(false, params[m_paramCtr]));
				m_paramCtr++;
			}
		}	
	}
	
	/**
	 * Creates a simplifier.  This will simplify repeatedly until a fixpoint
	 * is reached.
	 * @param script A Script object that will be used to check for equivalent
	 * formulas. 
	 */
	public SimplifyDDA(Script script) {
		this(script, true);
	}
	
	/**
	 * Creates a simplifier.  
	 * @param script A Script object that will be used to check for equivalent
	 * formulas. 
	 * @param simplifyRepeatedly true if the simplifier should run until a 
	 * fixpoint is reached.
	 */
	public SimplifyDDA(final Script script, boolean simplifyRepeatedly) {
		m_Script = script;
		m_True = m_Script.term("true");
		m_False = m_Script.term("false");
		m_SimplifyRepeatedly = simplifyRepeatedly;
	}
	
	/**
	 * Redundancy is a property of a subterm B with respect to its term A.
	 * The subterm B is called:
	 * <ul>
	 * <li> NON_RELAXING if term A is equivalent to the term, where B is replaced
	 * by false.
	 * <li> NON_CONSTRAINING if term A is equivalent to the term, where B is
	 * replaced by true.
	 * <li> NOT_REDUNDANT B is neither NON_REAXING nor NON_CONSTRAINING with
	 * respect to A.
	 * </ul>
	 */
	public enum Redundancy {
		NON_RELAXING, NON_CONSTRAINING, NOT_REDUNDANT
	}
	
	/**
	 * Checks if termA is equivalent to termB.
	 * Returns unsat if the terms are equivalent, sat if they are not and
	 * unknown if it is not possible to determine.
	 */
	public LBool checkEquivalence (Term termA, Term termB) throws SMTLIBException {
		Term equivalentTestTerm = m_Script.term("=", termA, termB);
		String checktype = null;
		try {
			checktype = (String) m_Script.getOption(":check-type");
			m_Script.setOption(":check-type", "FULL");
		} catch (UnsupportedOperationException ignored) {}
		LBool areTermsEquivalent = 
				Util.checkSat(m_Script, Util.not(m_Script, equivalentTestTerm));
		if (checktype != null)
			m_Script.setOption(":check-type", checktype);
		return areTermsEquivalent;
		
	}
	
	/**
	 * Checks if term is redundant, with respect to the critical constraint
	 * on the assertion stack.
	 * @return NON_CONSTRAINING if term is equivalent to true,
	 * NON_RELAXING if term is equivalent to true,
	 * NOT_REDUNDANT if term is not redundant.
	 */
	private Redundancy getRedundancy (Term term)
			throws SMTLIBException {
		LBool isTermConstraining =
				Util.checkSat(m_Script, Util.not(m_Script, term));
		if (isTermConstraining == LBool.UNSAT) {
			return Redundancy.NON_CONSTRAINING;
		}
				
		LBool isTermRelaxing = Util.checkSat(m_Script, term);
		if (isTermRelaxing == LBool.UNSAT) {
			return Redundancy.NON_RELAXING;
		}
		
		return Redundancy.NOT_REDUNDANT;
	}
	
	private static Term termVariable2constant(Script script, TermVariable tv) 
			throws SMTLIBException {
		String name = tv.getName() + "_const_" + tv.hashCode();
		Sort[] paramSorts = {};
		Sort resultSort = tv.getSort();
		script.declareFun(name, paramSorts, resultSort);
		Term result = script.term(name);
		return result;
	}
	
	public Term simplifyOnce(Term term) {
		m_termInfos = new HashMap<Term, TermInfo>(); 

		run(new TermCounter(term));
		run(new ContextCollector(false, term, new ArrayDeque<Term>()));
		run(new PrepareSimplifier(false, term));
		run(new Simplifier(false, term));
		Term output = popResult();

		m_termInfos = null;
		return output;
	}

	/**
	 * Return a Term which is equivalent to term but whose number of leaves is
	 * less than or equal to the number of leaves in term.
	 * @return term if each subterm of term is neither NON_CONSTRAINING
	 * nor NON_RELAXING. Otherwise return a copy of term, where each
	 * NON_CONSTRAINING subterm is replaced by true and each NON_RELAXING
	 * subterm is replaced by false
	 * @param term whose Sort is Boolean
	 */
	public Term getSimplifiedTerm(Term inputTerm) throws SMTLIBException {
//		m_Logger.debug("Simplifying " + term);
		/* We can only simplify boolean terms. */
		if (!inputTerm.getSort().getName().equals("Bool"))
			return inputTerm;
		Term term = inputTerm;
		m_Script.push(1);
		final TermVariable[] vars = term.getFreeVars();
		final Term[] values = new Term[vars.length];
		for (int i=0; i<vars.length; i++) {
			values[i] = termVariable2constant(m_Script, vars[i]);
		}
		term = m_Script.let(vars, values, term);

		term = new FormulaUnLet().unlet(term);

		Term output = simplifyOnce(term);
		if (m_SimplifyRepeatedly) {
			while (output != term) {
				term = output;
				output = simplifyOnce(term);
			}
		} else {
			term = output;
		}
		
		term = new TermTransformer() {
			@Override
			public void convert(Term term) {
				for (int i = 0; i < vars.length; i++)
					if (term == values[i])
						term = vars[i];
				super.convert(term);
			}
		}.transform(term);
		m_Script.pop(1);
		assert (checkEquivalence(inputTerm, term) == LBool.UNSAT) : "Simplification unsound?";
		return term;
	}
	
	/**
	 * Returns the contribution of a sibling to the critical constraint. This is
	 * either the sibling itself or its negation. The result is the negated
	 * sibling iff
	 * <ul>
	 * <li> the connective is "or"
	 * <li> the connective is "=>" and i==n-1
	 * </ul>
	 * 
	 * @param i Index of this sibling. E.g., sibling B has index 1 in the term
	 * (and A B C)
	 * @param n Number of all siblings. E.g., the term (and A B C) has three
	 * siblings.
	 */
	private Term negateSibling(Term sibling, String connective, int i, int n) {
		final boolean negate = (connective == "or" || connective == "=>" && i == n-1);
		if (negate) {
			return Util.not(m_Script, sibling);
		} else {
			return sibling;
		}
	}
	
	void pushContext(Term... context) {
		m_Script.push(1);
		for (Term t : context) {
			m_Script.assertTerm(t);
		}
	}

	void popContext() {
		m_Script.pop(1);
	}

	void setResult(boolean negated, Term term) {
		if (negated)
			term = Util.not(m_Script, term);
		assert (m_Result == null);
		m_Result = term;
	}

	Term popResult() {
		Term result = m_Result;
		m_Result = null;
		return result;
	}
}
