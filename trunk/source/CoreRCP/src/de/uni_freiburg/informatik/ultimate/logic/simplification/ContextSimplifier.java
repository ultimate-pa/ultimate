package de.uni_freiburg.informatik.ultimate.logic.simplification;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * This class performs contextual simplification of SMT formulae. Basic
 * transitions include
 * <pre>
 * simp(a&b,C) =
 *   (a<-simp(a,C&b),b<-simp(b,C&a))+,
 *   a&b
 *   
 * simp(a|b,C) =
 * 	(a<-simp(a,C& not b),b<-simp(b,C& not a))+,
 * 	a|b
 * 
 * simp(a->b,C) =
 * 	(a<-not simp(not a,C& not b),b<-simp(b,C&a))+,
 * 	a->b
 * 
 * simp(ite c t f,C) =
 * 	c<-simp(c,C),t<-simp(t,C&c),f<-simp(f,C& not c),
 * 	ite c t f
 * 
 * simp(Q f,C) =
 * 	Q simp(f,C)
 * </pre>
 * 
 * Finally, this simplifier provides a method to reduce the size of the formula
 * by introducing let bindings for all shared subterms.
 * @author Juergen Christ
 */
public class ContextSimplifier {
	private Theory m_Theory;
	private HashSet<Term> m_Context;
	private HashMap<HashSet<Term>, Term> m_EqNormalizer;
	
	public ContextSimplifier(Theory theory) {
		m_Theory = theory;
		m_Context = new HashSet<Term>();
		m_EqNormalizer = new HashMap<HashSet<Term>, Term>();
	}
	/**
	 * Contextual simplification routine.
	 * @param input Input term/formula.
	 * @return Simplified but still equivalent term/formula.
	 */
	public Term simplify(Term input) {
		if (input instanceof AnnotatedTerm) {
			AnnotatedTerm annot = (AnnotatedTerm)input;
			Term simp = simplify(annot.getSubterm());
			return simp == annot.getSubterm() ? 
					annot :
						m_Theory.annotatedTerm(annot.getAnnotations(),simp);
		}
		if (input instanceof ApplicationTerm) {
			if (input == m_Theory.TRUE || input == m_Theory.FALSE)
				return input;
			ApplicationTerm at = (ApplicationTerm)input;
			Term[] params = at.getParameters();
			/*
			 * simp(a|b,C) =
			 * 	(a<-simp(a,C& not b),b<-simp(b,C& not a))+,
			 * 	a|b
			 * 
			 * simp(a->b,C) =
			 * 	(a<-not simp(not a,C& not b),b<-simp(b,C&a))+,
			 * 	a->b
			 */
			FunctionSymbol fs = at.getFunction();
			if (fs == m_Theory.m_And) {
				/*
				 *  Bugfix: We can only remove params[i] if we add it here.
				 *  Otherwise, it is already in the outer context and we should
				 *  not touch it.
				 */
				boolean[] remove = new boolean[params.length];
				for (int i = 0; i < params.length; ++i)
					remove[i] = m_Context.add(params[i]);
				Term[] newparams = new Term[params.length];
				for (int i = 0; i < params.length; ++i) {
					if (remove[i])
						m_Context.remove(params[i]);
					newparams[i] = simplify(params[i]);
					remove[i] = m_Context.add(newparams[i]);
				}
				for (int i = 0; i < newparams.length; ++i) {
					if (remove[i])
						m_Context.remove(newparams[i]);
				}
				return m_Theory.and(newparams);
			}
			if (fs == m_Theory.m_Implies) {
				// Basic idea: transform to or, simplify, transform back
				Term[] negparams = new Term[params.length];
				System.arraycopy(params, 0, negparams, 0, params.length - 1);
				negparams[negparams.length - 1] = 
					m_Theory.not(params[params.length - 1]);
				boolean[] remove = new boolean[negparams.length];
				for (int i = 0; i < negparams.length; ++i)
					remove[i] = m_Context.add(negparams[i]);
				Term[] newparams = new Term[params.length];
				for (int i = 0; i < params.length; ++i) {
					if (remove[i])
						m_Context.remove(negparams[i]);
					negparams[i] = simplify(m_Theory.not(negparams[i]));
					newparams[i] = m_Theory.not(negparams[i]);
					remove[i] = m_Context.add(negparams[i]);
				}
				for (int i = 0; i < negparams.length; ++i) {
					if (remove[i])
						m_Context.remove(negparams[i]);
				}
				return m_Theory.or(newparams);
			}
			if (fs == m_Theory.m_Or) {
				Term[] negparams = new Term[params.length];
				boolean[] remove = new boolean[params.length];
				for (int i = 0; i < params.length; ++i) {
					negparams[i] = m_Theory.not(params[i]);
					remove[i] = m_Context.add(negparams[i]);
				}
				Term[] newparams = new Term[params.length];
				for (int i = 0; i < params.length; ++i) {
					if (remove[i])
						m_Context.remove(negparams[i]);
					newparams[i] = simplify(params[i]);
					negparams[i] = m_Theory.not(newparams[i]);
					remove[i] = m_Context.add(negparams[i]);
				}
				for (int i = 0; i < negparams.length; ++i) {
					if (remove[i])
						m_Context.remove(negparams[i]);
				}
				return m_Theory.or(newparams);
			}
			if (fs == m_Theory.m_Not) {
				return m_Theory.not(simplify(params[0]));
			}
			if (fs.isIntern()) {
				if (fs.getName().equals("ite")) {
					Term c = simplify(params[0]);
					boolean removec = m_Context.add(c);
					Term t = simplify(params[1]);
					if (removec)
						m_Context.remove(c);
					Term notc = m_Theory.not(c);
					boolean removenotc = m_Context.add(notc);
					Term f = simplify(params[2]);
					if (removenotc)
						m_Context.remove(notc);
					return m_Theory.ifthenelse(c, t, f);
				} else if (fs.getName().equals("distinct") || 
						fs == m_Theory.m_Xor) {
					HashSet<ConstantTerm> consts = new HashSet<ConstantTerm>();
					for (Term p : params) {
						if (p instanceof ConstantTerm &&
								!consts.add((ConstantTerm)p))
							return m_Theory.FALSE;
					}
					input = m_Theory.not(m_Theory.equals(params));
				} else if (fs.getName().equals("=")) {
					HashSet<Term> argsSet =
						new HashSet<Term>(params.length, 1.0f);
					Collections.addAll(argsSet, params);
					Term norm = m_EqNormalizer.get(argsSet);
					if (norm != null && norm != input)
						return simplify(norm);
					// Boolean terms...
					if (params[0].getSort() == m_Theory.getBooleanSort()) {
						// simplify the subterms
						// Argument set does not grow...
						HashSet<Term> newparams =
							new HashSet<Term>(params.length, 1.0f);
						for (Term p : params)
							// Don't make additional assumptions in the context.
							// We cannot distinguish the branch here...
							newparams.add(simplify(p));
						for (Term p : newparams) {
							if (newparams.contains(m_Theory.not(p)))
								return m_Theory.FALSE;
						}
						Term res = m_Theory.equals(
								newparams.toArray(new Term[newparams.size()]));
						m_EqNormalizer.put(newparams, res);
						return res;
					} else {
						// Try to detect constants
						ConstantTerm first = null;
						for (Term p : params) {
							if (p instanceof ConstantTerm) {
								if (first == null)
									first = (ConstantTerm) p;
								else if (first != p)
									return m_Theory.FALSE;
							}
						}
						input = m_Theory.equals(params);
						m_EqNormalizer.put(argsSet, input);
					}
				}
			}
			if (m_Context.contains(input))
				return m_Theory.TRUE;
			if (m_Context.contains(m_Theory.not(input)))
				return m_Theory.FALSE;
			return input;
		}
		if (input instanceof QuantifiedFormula) {
			QuantifiedFormula qf = (QuantifiedFormula)input;
			Term simp = simplify(qf.getSubformula());
			return simp == qf.getSubformula() ?
					input :
						qf.getQuantifier() == QuantifiedFormula.EXISTS ?
								m_Theory.exists(qf.getVariables(),simp) :
									m_Theory.forall(qf.getVariables(),simp);
		}
		return input;
	}
	/**
	 * Closure of the simplification procedure. The simplifier is invoked until
	 * no change between input and output can be detected. That is
	 * <code>input == simplify(input)</code> holds after termination.
	 * <br/>
	 * Note that this formula might be very slow since it might take some steps
	 * to compute this closure.
	 * @param input Formula to simplify.
	 * @return Maximally simplified formula.
	 */
	public Term closuresimplify(Term input) {
		Term result = simplify(input);
		while (input != result) {
			input = result;
			result = simplify(input);
		}
		return result;
	}
}
