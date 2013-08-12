package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.linearTerms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;



/**
 * Try to eliminate existentially quantified variables in terms.
 * Therefore we use that the term ∃v.v=c∧φ[v] is equivalent to term φ[c].
 * Resp. we use that the term ∀v.v!=c∨φ[v] is equivalent to term φ[c].
 */
public class DestructiveEqualityResolution {
	
	static boolean USE_UPD = true;
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	/**
	 * Returns equivalent formula. Quantifier is dropped if quantified
	 * variable not in formula. Quantifier is eliminated if this can be done
	 * by using a naive "destructive equality resolution".
	 */
	public static Term quantifier(Script script, int quantifier, 
			TermVariable[] vars, Term body,	Term[]... patterns) {
		Set<TermVariable> occuringVars = 
				new HashSet<TermVariable>(Arrays.asList(body.getFreeVars()));
		Set<TermVariable> remaning = new HashSet<TermVariable>(vars.length);
		for (TermVariable tv : vars) {
			if (occuringVars.contains(tv)) {
				remaning.add(tv);
			}
		}
		Term reduced;
		reduced = derSimple(script, quantifier, body, remaning);
		if (remaning.isEmpty()) {
			return reduced;
		}
		if (USE_UPD) {
			reduced = updSimple(script, quantifier, reduced, remaning);
			if (remaning.isEmpty()) {
				return reduced;
			} 
		}
		return script.quantifier(quantifier, 
					remaning.toArray(new TermVariable[0]), reduced, patterns);
	}
	
	/**
	 * Try to eliminate the variables vars = {x_1,...,x_n} in term φ_1∧...∧φ_m.
	 * Therefore we use the following approach, which we call 
	 * Unconnected Parameter Drop.
	 * If X is a subset of {x_1,...,x_n} and Φ is a subset {φ_1,...,φ_m} such 
	 * that
	 * - variables in X occur only in term of Φ, and
	 * - terms in Φ contain only variables of X, and
	 * - the conjunction of all term in Φ is satisfiable.
	 * Then we can remove the conjuncts Φ and the quantified variables X from
	 * φ_1∧...∧φ_m and obtain an equivalent formula.
	 * 
	 * Is only sound if there are no uninterpreted function symbols in the term
	 * TODO: extend this to uninterpreted function symbols
	 */
	public static Term updSimple(Script script, int quantifier, Term term, 
			Set<TermVariable> vars) {
		if (quantifier == QuantifiedFormula.FORALL) {
			// not implemented yet.
			return term;
		} else {
			Set<TermVariable> occuringVars = 
					new HashSet<TermVariable>(Arrays.asList(term.getFreeVars()));
			Set<Term> conjuncts = getConjuncts(term);
			ConnectionPartition connection = new ConnectionPartition();
			for (Term conjunct : conjuncts) {
				connection.addTerm(conjunct);
			}
			List<TermVariable> removeableTvs = new ArrayList<TermVariable>();
			List<TermVariable> unremoveableTvs = new ArrayList<TermVariable>();
			List<Term> removeableTerms = new ArrayList<Term>();
			List<Term> unremoveableTerms = new ArrayList<Term>();
			for (Set<TermVariable> connectedVars : connection.getConnectedVariables()) {
				Set<Term> terms = connection.getTermsOfConnectedVariables(connectedVars);
				if (isSuperfluousComponent(script, terms, connectedVars, vars)) {
					removeableTvs.addAll(connectedVars);
					removeableTerms.addAll(terms);
				} else {
					unremoveableTvs.addAll(connectedVars);
					unremoveableTerms.addAll(terms);
				}
			}
			List<Term> termsWithoutTvs = connection.getTermsWithOutTvs();
			assert occuringVars.size() == removeableTvs.size() + unremoveableTvs.size();
			assert conjuncts.size() == removeableTerms.size() + unremoveableTerms.size() + termsWithoutTvs.size();
			for (Term termWithoutTvs : termsWithoutTvs) {
				LBool sat = Util.checkSat(script, termWithoutTvs);
				if (sat == LBool.UNSAT) {
					vars.clear();
					return script.term("false");
				} else if (sat == LBool.SAT) {
					// we drop this term its equivalent to true
				} else {
					throw new AssertionError("expecting sat or unsat");
				}
			}
			if (removeableTerms.isEmpty()) {
				s_Logger.debug(new DebugMessage("not eliminated quantifier via UPD for {0}", occuringVars));
				return term;
			} else {
				vars.removeAll(removeableTvs);
				s_Logger.debug(new DebugMessage("eliminated quantifier via UPD for {0}", removeableTvs));
				return Util.and(script, unremoveableTerms.toArray(new Term[0]));
			}
		}
	}
	
	/**
	 * Return true if connectedVars is a subset of quantifiedVars and the
	 * conjunction of terms is satisfiable.
	 */
	public static boolean isSuperfluousComponent(Script script, Set<Term> terms,  
			Set<TermVariable> connectedVars, Set<TermVariable> quantifiedVars) {
		if (quantifiedVars.containsAll(connectedVars)) {
			Term conjunction = Util.and(script, terms.toArray(new Term[0]));
			if (Util.checkSat(script, conjunction) == LBool.SAT) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * If term is a conjunction return all conjuncts, otherwise return term.
	 */
	public static Set<Term> getConjuncts(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().getName().equals("and")) {
				return new HashSet<Term>(Arrays.asList(appTerm.getParameters()));
			}
		}
		return Collections.singleton(term);
	}
	
	/**
	 * Partition set of terms into equivalence classes. 
	 * We call two terms connected if both share a common free variable.
	 * we define two terms to be equivalent (resp. this partition) if they
	 * are in the transitive closure of the connection relation.
	 */
	public static class ConnectionPartition {
		Map<TermVariable, Set<Term>> m_Tv2Terms = new HashMap<TermVariable, Set<Term>>();
		UnionFind<TermVariable> unionFind = new UnionFind<TermVariable>();
		List<Term> m_TermWithoutTvs = new ArrayList<Term>();
		
		void addTerm(Term term) {
			TermVariable[] tvs = term.getFreeVars();
			if (tvs.length == 0) {
				m_TermWithoutTvs.add(term);
				return;
			}
			TermVariable firstTv = tvs[0];
			add(term, firstTv);
			if (unionFind.find(firstTv) == null) {
				unionFind.makeEquivalenceClass(firstTv);
			}
			for (int i=1; i < tvs.length; i++) {
				add(term, tvs[i]);
				if (unionFind.find(tvs[i]) == null) {
					unionFind.makeEquivalenceClass(tvs[i]);					
				} 
				if (unionFind.find(firstTv).equals(unionFind.find(tvs[i]))) {
					// already in same equivalence class
				} else {
					unionFind.union(tvs[i], firstTv);
				}
			}
		}
		
		private void add(Term term, TermVariable tv) {
			Set<Term> terms = m_Tv2Terms.get(tv);
			if (terms == null) {
				terms = new HashSet<Term>();
				m_Tv2Terms.put(tv, terms);
			}
			terms.add(term);
		}
		
		Set<Set<TermVariable>> getConnectedVariables() {
			return unionFind.getEquivalenceClass();
		}
		
		Set<Term> getTermsOfConnectedVariables(Set<TermVariable> connectedVars) {
			Set<Term> result = new HashSet<Term>();
			for (TermVariable tv : connectedVars) {
				result.addAll(m_Tv2Terms.get(tv));
			}
			return result;
		}
		
		List<Term> getTermsWithOutTvs() {
			return m_TermWithoutTvs;
		}
		
	}
	
	
	
	/**
	 * Try to eliminate the variables vars in term.
	 * Let vars =  {x_1,...,x_n} and term = φ. Returns a term that is 
	 * equivalent to ∃x_1,...,∃x_n φ, but were variables are removed.
	 * Successfully removed variables are also removed from vars.
	 * Analogously for universal quantification.
	 */
	public static Term derSimple(Script script, int quantifier, Term term, 
			Collection<TermVariable> vars) {
		Term resFormula = new FormulaUnLet().unlet(term);
		Iterator<TermVariable> it = vars.iterator();
		while(it.hasNext()) {
			if (!(resFormula instanceof ApplicationTerm)) {
				s_Logger.debug("abort DER: No application Term");
				return resFormula;
			}
			ApplicationTerm appTerm = (ApplicationTerm) resFormula;
			TermVariable tv = it.next();

			Term[] oldParams = appTerm.getParameters();
			if (quantifier == QuantifiedFormula.EXISTS) {
				if (!appTerm.getFunction().getName().equals("and")) {
					s_Logger.debug("abort DER: existential quantification but no conjunction");
					return resFormula;
				}
			} else if (quantifier == QuantifiedFormula.FORALL) {
				if (!appTerm.getFunction().getName().equals("or")) {
					s_Logger.debug("abort DER: universal quantification but no disjunction");
					return resFormula;
				}
			} else {
				throw new AssertionError("unknown quantifier");
			}
			EqualityInformation eqInfo = getEqinfo(script, tv, oldParams, quantifier);
			if (eqInfo == null) {
				s_Logger.debug(new DebugMessage("not eliminated quantifier via DER for {0}", tv));
			} else {
				it.remove();
				s_Logger.debug(new DebugMessage("eliminated quantifier via DER for {0}", tv));
				Term[] newParams = new Term[oldParams.length-1];
				Map<TermVariable, Term> substitutionMapping = 
						Collections.singletonMap(eqInfo.getVariable(), eqInfo.getTerm());
				Substitution substitution = new Substitution(substitutionMapping, script);
				for (int i=0; i<eqInfo.getIndex(); i++) {
					newParams[i] = substitution.transform(oldParams[i]);
				}
				for (int i=eqInfo.getIndex()+1; i<oldParams.length; i++) {
					newParams[i-1] = substitution.transform(oldParams[i]);
				}
				if (quantifier == QuantifiedFormula.EXISTS) {
					resFormula = Util.and(script, newParams);
				} else if (quantifier == QuantifiedFormula.FORALL) {
					resFormula = Util.or(script, newParams);
				} else {
					throw new AssertionError("unknown quantifier");
				}
			}
		}
		return resFormula;
	}
	
	private static EqualityInformation getEqinfo(Script script, TermVariable tv,
			Term[] terms, int quantifier) {
		for (int i=0; i<terms.length; i++) {
			if (!(terms[i] instanceof ApplicationTerm)) {
				continue;
			}
			ApplicationTerm appTerm = (ApplicationTerm) terms[i];
			Term lhs;
			Term rhs;
			if (quantifier == QuantifiedFormula.EXISTS) {
				if (appTerm.getFunction().getName().equals("=")) {
					if (appTerm.getParameters().length != 2) {
						throw new UnsupportedOperationException();
					}
					//TODO test this here
					lhs = appTerm.getParameters()[0];
					rhs = appTerm.getParameters()[1];
					
				} else {
					continue;
				}
			} else if (quantifier == QuantifiedFormula.FORALL) {
				if (appTerm.getFunction().getName().equals("not")) {
					Term[] negParams = appTerm.getParameters();
					assert negParams.length == 1;
					Term negTerm = negParams[0];
					if (negTerm instanceof ApplicationTerm) {
						ApplicationTerm negAppTerm = (ApplicationTerm) negTerm;
						if (negAppTerm.getFunction().getName().equals("=")) {
							if (appTerm.getParameters().length != 2) {
								throw new UnsupportedOperationException();
							}
							lhs = negAppTerm.getParameters()[0];
							rhs = negAppTerm.getParameters()[1];
						} else {
							continue;
						}
					} else {
						continue;
					}
					
				} else {
					continue;
				}
			} else {
				throw new AssertionError("unknown quantifier");
			}
			boolean allowRewrite = true;
			if (allowRewrite) {
				if (Arrays.asList(appTerm.getFreeVars()).contains(tv) && rhs.getSort().isNumericSort()) {
					AffineRelation affRel = new AffineRelation(appTerm);
					if (!affRel.translationFailed()) {
						ApplicationTerm eqTerm = (ApplicationTerm) affRel.onLeftHandSideOnly(script, tv);
						return new EqualityInformation(i, tv, eqTerm.getParameters()[1]);
					}
				}
			}
			if (lhs.equals(tv) && !Arrays.asList(rhs.getFreeVars()).contains(tv)) {
				return new EqualityInformation(i, tv, rhs);
			}
			if (rhs.equals(tv) && !Arrays.asList(lhs.getFreeVars()).contains(tv)) {
				return new EqualityInformation(i, tv, lhs);
			}

		}
		// no equality information found
		return null;
	}

	private static class EqualityInformation {
		private final int m_Index;
		private final TermVariable m_Variable;
		private final Term m_Term;
		public EqualityInformation(int index, TermVariable variable, Term term) {
			m_Index = index;
			m_Variable = variable;
			m_Term = term;
		}
		public int getIndex() {
			return m_Index;
		}
		public TermVariable getVariable() {
			return m_Variable;
		}
		public Term getTerm() {
			return m_Term;
		}
		
	}
	

	
	
	/**
	 * Find term φ such that term implies tv == φ. 
	 */
	private static Term findEqualTermExists(TermVariable tv, Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol sym = appTerm.getFunction();
			Term[] params = appTerm.getParameters();
			if (sym.getName().equals("=")) {
				int tvOnOneSideOfEquality = tvOnOneSideOfEquality(tv, params);
				if (tvOnOneSideOfEquality == -1) {
					return null;
				} else {
					assert (tvOnOneSideOfEquality == 0 || tvOnOneSideOfEquality == 1);
					return params[tvOnOneSideOfEquality];				
				}
			} else if (sym.getName().equals("and")) {
				for (Term param : params) {
					Term equalTerm = findEqualTermExists(tv, param);
					if (equalTerm != null) {
						return equalTerm;
					}
				}
				return null;
			} else {
				return null;
			}
		} else {
			return null;
		}
	}
	
	
	/**
	 * Find term φ such that tv != φ implies term 
	 */
	private static Term findEqualTermForall(TermVariable tv, Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol sym = appTerm.getFunction();
			Term[] params = appTerm.getParameters();
			if (sym.getName().equals("not")) {
				assert params.length == 1;
				if (params[0] instanceof ApplicationTerm) {
					appTerm = (ApplicationTerm) params[0];
					sym = appTerm.getFunction();
					params = appTerm.getParameters();
					if (sym.getName().equals("=")) {
						int tvOnOneSideOfEquality = tvOnOneSideOfEquality(tv, params);
						if (tvOnOneSideOfEquality == -1) {
							return null;
						} else {
							assert (tvOnOneSideOfEquality == 0 || tvOnOneSideOfEquality == 1);
							return params[tvOnOneSideOfEquality];				
						}
					} else {
						return null;
					}
				} else {
					return null;
				}
			} else if (sym.getName().equals("or")) {
				for (Term param : params) {
					Term equalTerm = findEqualTermForall(tv, param);
					if (equalTerm != null) {
						return equalTerm;
					}
				}
				return null;
		} else {
				return null;
			}
		} else {
			return null;
		}
	}
	
	
	/**
     * return <ul>
	 * <li> 0 if right hand side of equality is tv and left hand side does not
	 *  contain tv
  	 * <li> 1 if left hand side of equality is tv and right hand side does not
	 *  contain tv
	 * <li> -1 otherwise
	 * </ul>
	 * 
	 */
	private static int tvOnOneSideOfEquality(TermVariable tv, Term[] params) {
		if (params.length != 2) {
			s_Logger.warn("Equality of length " + params.length);
		}
		if (params[0] == tv) {
			final boolean rightHandSideContainsTv = 
					Arrays.asList(params[1].getFreeVars()).contains(tv);
			if (rightHandSideContainsTv) {
				return -1;
			}
			else {
				return 1;
			}
		} else if (params[1] == tv) {
			final boolean leftHandSideContainsTv = 
					Arrays.asList(params[0].getFreeVars()).contains(tv);
			if (leftHandSideContainsTv) {
				return -1;
			}
			else {
				return 0;
			}
		}
		return -1;
	}

}
