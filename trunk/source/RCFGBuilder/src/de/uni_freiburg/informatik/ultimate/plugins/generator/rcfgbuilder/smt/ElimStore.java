package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;

public class ElimStore {
	
	

	public ElimStore(Script script) {
		super();
		m_Script = script;
	}

	private final Script m_Script;
	private Term m_WriteIndex;
	private Term m_Data;
	private Term m_NewArray;
	public Term elim(TermVariable tv, Term term) {
		assert tv.getSort().isArraySort();
		Set<Term> conjuncts = DestructiveEqualityResolution.getConjuncts(term);
		HashSet<Term> others = new HashSet<Term>();
		for (Term conjunct : conjuncts) {
			if (conjunct instanceof ApplicationTerm) {
				ApplicationTerm eqAppTerm = (ApplicationTerm) conjunct;
				if (eqAppTerm.getFunction().getName().equals("=")) {
					if (eqAppTerm.getParameters().length == 2) {
						if (eqAppTerm.getParameters()[0] instanceof ApplicationTerm) {
							ApplicationTerm appTerm = (ApplicationTerm) eqAppTerm.getParameters()[0];
							if (appTerm.getFunction().getName().equals("store")) {
								if (appTerm.getParameters()[0].equals(tv)) {
									assert appTerm.getParameters().length == 3;
									m_NewArray = eqAppTerm.getParameters()[1];
									m_WriteIndex = appTerm.getParameters()[1];
									m_Data = appTerm.getParameters()[2];
									continue;
								}
							}
						}
						if (eqAppTerm.getParameters()[1] instanceof ApplicationTerm) {
							ApplicationTerm appTerm = (ApplicationTerm) eqAppTerm.getParameters()[1];
							if (appTerm.getFunction().getName().equals("store")) {
								if (appTerm.getParameters()[0].equals(tv)) {
									assert appTerm.getParameters().length == 3;
									m_NewArray = eqAppTerm.getParameters()[0];
									m_WriteIndex = appTerm.getParameters()[1];
									m_Data = appTerm.getParameters()[2];
									continue;
								}
							}
						}
					}
					
				}
			}
			others.add(conjunct);
		}
		if (others.size() != conjuncts.size() -1) {
			throw new UnsupportedOperationException("not exactly one store");
		}
		assert m_WriteIndex != null;
		assert m_Data != null;
		Term othersT = Util.and(m_Script, others.toArray(new Term[0])); 
		Set<ApplicationTerm> selectTerms = (new ApplicationTermFinder("select")).findMatchingSubterms(term);
		Map<Term,ApplicationTerm> arrayReads = new HashMap<Term,ApplicationTerm>();
		for (ApplicationTerm selectTerm : selectTerms) {
			if (selectTerm.getParameters()[0].equals(tv)) {
				Term index = selectTerm.getParameters()[1];
				arrayReads.put(index, selectTerm);
			}
		}
		
		m_Script.push(1);
		ScopedHashMap<TermVariable, Term> tv2constant = new ScopedHashMap<TermVariable, Term>();
		assertTermWithTvs(tv2constant, m_Script, othersT);
		
		UnionFind<Term> uf = new UnionFind<Term>();
		for (Term index : arrayReads.keySet()) {
			uf.makeEquivalenceClass(index);
			Term eqTerm = getEquivalentTerm(index, uf, tv2constant);
			if (eqTerm != null) {
				uf.union(index, eqTerm);
			}
		}
		Term writeIndexEqClass = getEquivalentTerm(m_WriteIndex, uf, tv2constant);
		HashSet<Term> distinctIndices = new HashSet<Term>();
		HashSet<Term> unknownIndices = new HashSet<Term>();
		divideInDistinctAndUnknown(m_WriteIndex, uf, distinctIndices, unknownIndices, tv2constant);
		if (!unknownIndices.isEmpty()) {
			throw new UnsupportedOperationException();
		}
		m_Script.pop(1);
		
		
		Map<Term,Term> substitutionMapping = new HashMap<Term,Term>();
		for (Term distinctIndexRep : distinctIndices) {
			for (Term distTerm : uf.getEquivalenceClassMembers(distinctIndexRep)) {
				ApplicationTerm oldSelectTerm = arrayReads.get(distTerm);
				assert oldSelectTerm.getFunction().getName().equals("select");
				assert oldSelectTerm.getParameters().length == 2;
				assert oldSelectTerm.getParameters()[0] == tv;
				Term newSelectTerm = m_Script.term("select", m_NewArray, oldSelectTerm.getParameters()[1]);
				substitutionMapping.put(oldSelectTerm, newSelectTerm);
			}
		}
		
		if (writeIndexEqClass != null) {
			for(Term writeIndexEqTerm : uf.getEquivalenceClassMembers(writeIndexEqClass)) {
				TermVariable freshVar = writeIndexEqTerm.getTheory().createFreshTermVariable(writeIndexEqTerm.toStringDirect(), writeIndexEqTerm.getSort());
				substitutionMapping.put(writeIndexEqTerm, freshVar);
			}
		}
		Term result = (new SafeSubstitution(m_Script, substitutionMapping)).transform(othersT);
		Term newData = (new SafeSubstitution(m_Script, substitutionMapping)).transform(m_Data);
		Term t = m_Script.term("=", m_Script.term("select", m_NewArray, m_WriteIndex), newData);
		result = Util.and(m_Script, result, t);
		result.toString();
		return result;
	}
	
	private Term getEquivalentTerm(Term term, UnionFind<Term> uf, ScopedHashMap<TermVariable, Term> tv2constant) {
		for (Term representative : uf.getAllRepresentatives()) {
			assert representative != null;
			Term negated = m_Script.term("distinct", representative, term);
			m_Script.push(1);
			tv2constant.beginScope();
			assertTermWithTvs(tv2constant, m_Script, negated);
			LBool sat = m_Script.checkSat();
			tv2constant.endScope();
			m_Script.pop(1);
			boolean equal = (sat == LBool.UNSAT);
			if (equal) {
				return representative;
			}
		}
		return null;
	}
	
	private void divideInDistinctAndUnknown(Term term, UnionFind<Term> uf, 
			HashSet<Term> distinctTerms, HashSet<Term> unknownTerms, ScopedHashMap<TermVariable, Term> tv2constant) {
		for (Term representative : uf.getAllRepresentatives()) {
			assert representative != null;
			Term test = m_Script.term("=", representative, term);
			m_Script.push(1);
			tv2constant.beginScope();
			assertTermWithTvs(tv2constant, m_Script, test);
			LBool sat = m_Script.checkSat();
			tv2constant.endScope();
			m_Script.pop(1);
			boolean distinct = (sat == LBool.UNSAT);
			if (distinct) {
				distinctTerms.add(representative);
			} else {
				unknownTerms.add(representative);
			}
		}
	}
	
	/**
	 * assert term, replace TermVariable by constants in advance, replace
	 * by constants defined by mapping, if no constant defined by mapping
	 * declare constant and add to mapping
	 */
	public void assertTermWithTvs(Map<TermVariable, Term> mapping, Script script, Term term) {
		for (TermVariable tv :term.getFreeVars()) {
			if (!mapping.containsKey(tv)) {
				String name = "arrayElim_" + tv.getName();
				script.declareFun(name, new Sort[0], tv.getSort());
				Term constant = script.term(name);
				mapping.put(tv, constant);
			}
		}
		Term renamed = (new Substitution(mapping, script)).transform(term);
		m_Script.assertTerm(renamed);
	}
	
}
