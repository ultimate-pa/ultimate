package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class SubstitutionManager {
	
	private int m_Depth = -1;
	private List<Substitution> m_Substs;
	
	private AbstractOneTermCmd m_Cmd;
	
	public SubstitutionManager(AbstractOneTermCmd cmd) {
		m_Cmd = cmd;
	}
	
	public boolean deepen() {
		++m_Depth;
		return computeSubsts();
	}
	
	/**
	 * Notification of a test failure.  Steps all substitutions one step further
	 * and, hence, misses some of the potentially exponentially many
	 * substitutions.
	 * @return Does this depth still has some substitutions?
	 */
	public boolean failed() {
		stepSubsts();
		return !m_Substs.isEmpty();
	}
	
	private Substitution getSubstition(Term t) {
		if (t instanceof AnnotatedTerm) {
			AnnotatedTerm at = (AnnotatedTerm) t;
			for (Annotation a : at.getAnnotations())
				if (a.getKey().equals(":named"))
					// Cannot substitute at this level
					return null;
			// No names => Ignore annotations
			return new ReplaceByTerm(t, at.getSubterm());
		} else if (t.getSort() == t.getTheory().getBooleanSort()) {
			// Try to replace by true
			return new ReplaceByTerm(t, t.getTheory().TRUE);
		} else if (t.getSort().isNumericSort()) {
			return new ReplaceByTerm(t, t.getSort().getName().equals("Int") ?
					t.getTheory().numeral(BigInteger.ZERO) :
						t.getTheory().decimal(BigDecimal.ZERO));
		} else if (t instanceof ApplicationTerm) {
			// I guess this is always the case...
			ApplicationTerm at = (ApplicationTerm) t;
			if (at.getParameters().length > 0) {
				if (at.getFunction().getName().equals("store"))
					return new ReplaceByTerm(t, at.getParameters()[1]);
				return new ReplaceByFreshTerm(t);
			}
		}
		// Cannot replace TermVariables or ConstantTerms
		return null;
	}
	
	private Substitution getNextSubstitution(Substitution subst) {
		Term t = subst.getMatch();
		if (subst instanceof ReplaceByFreshTerm) {
			ApplicationTerm at = (ApplicationTerm) t;
			if (at.getFunction().getName().equals("ite"))
				return new ReplaceByTerm(t, at.getParameters()[1]);
			return null;
		}
		Theory theory = t.getTheory();
		ReplaceByTerm r = (ReplaceByTerm) subst;
		if (t instanceof AnnotatedTerm) {
			assert r.m_Replacement == ((AnnotatedTerm) t).getSubterm();
			return null;
		}
		if (r.m_Replacement == theory.TRUE)
			return new ReplaceByTerm(t, theory.FALSE);
		if (r.m_Replacement == theory.FALSE) {
			if (t instanceof ApplicationTerm) {
				ApplicationTerm at = (ApplicationTerm) t;
				/* I prefer to apply simplification after reduction.  Then, I
				 * can remove neutrals produced by reductions of lower levels,
				 * remove unused let- and quantifier-bindings.
				 */
//				// Neutrals
//				if (at.getFunction() == theory.m_And || 
//						at.getFunction() == theory.m_Or) {
//					Term neutral = at.getFunction() == theory.m_And ?
//							theory.TRUE : theory.FALSE;
//					LinkedHashSet<Term> newParams = new LinkedHashSet<Term>();
//					for (Term p : at.getParameters()) {
//						if (p != neutral)
//							newParams.add(p);
//					}
//					if (newParams.size() != at.getParameters().length) {
//						// Otherwise replace by true/false should succeed...
//						assert newParams.size() > 0;
//						if (newParams.size() == 1)
//							return new ReplaceByTerm(
//									newParams.iterator().next());
//						return new ReplaceByTerm(theory.term(at.getFunction(),
//								newParams.toArray(new Term[newParams.size()])));
//					}
//				}// neutrals
				// replace f-app
				if (at.getParameters().length > 0)
					return new ReplaceByFreshTerm(t);
			} // application term
			// give up
			return null;
		} else if (t instanceof ApplicationTerm) {
			// Can be either neutrals or ite or store
			ApplicationTerm at = (ApplicationTerm) t;
			if (at.getFunction().getName().equals("ite")) {
				if (r.m_Replacement == at.getParameters()[0])
					return new ReplaceByTerm(t, at.getParameters()[1]);
			} else if (at.getFunction().getName().equals("store") &&
					r.m_Replacement == at.getParameters()[0])
				return new ReplaceByFreshTerm(t);
			if (at.getParameters().length > 0)
				return new ReplaceByFreshTerm(t);
		}
		return null;
	}
	
	private boolean computeSubsts() {
		TermCollector tc = new TermCollector(m_Depth);
		tc.add(m_Cmd.getTerm());
		List<Term> found = tc.getTerms();
		m_Substs = new ArrayList<Substitution>(found.size());
		for (Term t : found) {
			Substitution subst = getSubstition(t);
			if (subst != null)
				m_Substs.add(subst);
		}
		return !found.isEmpty();
	}
	
	private void stepSubsts() {
		List<Substitution> old = m_Substs;
		m_Substs = new ArrayList<Substitution>(old.size());
		for (Substitution cur : old) {
			if (cur.isActive())
				continue;
			Substitution next = getNextSubstitution(cur);
			if (next != null)
				m_Substs.add(next);
		}
	}
	
	public List<Substitution> getSubstitutions() {
		return m_Substs;
	}

	public int getDepth() {
		return m_Depth;
	}
	
}
