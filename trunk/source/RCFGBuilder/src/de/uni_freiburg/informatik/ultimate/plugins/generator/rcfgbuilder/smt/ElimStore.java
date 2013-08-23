package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;

public class ElimStore {

	private Script m_Script;
	private Term m_WriteIndex;
	private Term m_Data;
	private Term m_NewArray;
	public void elim(TermVariable tv, Term term) {
		assert tv.getSort().isArraySort();
		Set<Term> conjuncts = DestructiveEqualityResolution.getConjuncts(term);
		HashSet<Term> others = new HashSet<Term>();
		for (Term conjunct : conjuncts) {
			if (conjunct instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) conjunct;
				if (appTerm.getFunction().getName().equals("store")) {
					if (appTerm.getParameters()[0].equals(tv)) {
						assert appTerm.getParameters().length == 3;
						m_NewArray = appTerm.getParameters()[0];
						m_WriteIndex = appTerm.getParameters()[1];
						m_Data = appTerm.getParameters()[2];
						continue;
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
		Set<ApplicationTerm> selectTerms = (new ApplicationTermFinder("select")).findMatchingSubterms(othersT);
		Map<Term,ApplicationTerm> arrayReads = new HashMap<Term,ApplicationTerm>();
		for (ApplicationTerm selectTerm : selectTerms) {
			if (selectTerm.getParameters()[0].equals(tv)) {
				Term index = selectTerm.getParameters()[1];
				arrayReads.put(index, selectTerm);
			}
		}
		
		m_Script.push(1);
		m_Script.assertTerm(othersT);
		
		UnionFind<Term> uf = new UnionFind<Term>();
		for (Term index : arrayReads.keySet()) {
			uf.makeEquivalenceClass(index);
			Term eqTerm = getEquivalentTerm(index, uf);
			if (eqTerm != null) {
				uf.union(index, eqTerm);
			}
		}
		Term writeIndexEqClass = getEquivalentTerm(m_WriteIndex, uf);
		HashSet<Term> distinctIndices = new HashSet<Term>();
		HashSet<Term> unknownIndices = new HashSet<Term>();
		divideInDistinctAndUnknown(m_WriteIndex, uf, distinctIndices, unknownIndices);
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
		
		
		
		
	}
	
	private Term getEquivalentTerm(Term term, UnionFind<Term> uf) {
		for (Term representative : uf.getAllRepresentatives()) {
			assert representative != null;
			Term negated = m_Script.term("distinct", representative, term);
			m_Script.push(1);
			m_Script.assertTerm(negated);
			LBool sat = m_Script.checkSat();
			m_Script.pop(1);
			boolean equal = (sat == LBool.UNSAT);
			if (equal) {
				return representative;
			}
		}
		return null;
	}
	
	private void divideInDistinctAndUnknown(Term term, UnionFind<Term> uf, 
			HashSet<Term> distinctTerms, HashSet<Term> unknownTerms) {
		for (Term representative : uf.getAllRepresentatives()) {
			assert representative != null;
			Term test = m_Script.term("=", representative, term);
			m_Script.push(1);
			m_Script.assertTerm(test);
			LBool sat = m_Script.checkSat();
			m_Script.pop(1);
			boolean distinct = (sat == LBool.UNSAT);
			if (distinct) {
				distinctTerms.add(representative);
			} else {
				unknownTerms.add(representative);
			}
		}
	}
	
}
