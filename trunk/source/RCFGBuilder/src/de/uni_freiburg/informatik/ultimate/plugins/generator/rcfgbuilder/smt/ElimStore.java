package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.DestructiveEqualityResolution.EqualityInformation;
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
		Term[] conjuncts = DestructiveEqualityResolution.getConjuncts(term);
		HashSet<Term> others = new HashSet<Term>();
		for (Term conjunct : conjuncts) {
			if (m_NewArray == null) {
				ArrayUpdate au = ArrayUpdate.getArrayUpdate(conjunct, tv);
				if (au != null) {
					m_WriteIndex = au.getIndex();
					m_NewArray = au.getNewArray();
					m_Data = au.getData();
					continue;
				}
			}
			others.add(conjunct);
		}
		Term othersT = Util.and(m_Script, others.toArray(new Term[0])); 
		Set<ApplicationTerm> selectTerms = (new ApplicationTermFinder("select")).findMatchingSubterms(term);
		Map<Term,ApplicationTerm> arrayReads = new HashMap<Term,ApplicationTerm>();
		for (ApplicationTerm selectTerm : selectTerms) {
			if (selectTerm.getParameters()[0].equals(tv)) {
				Term index = selectTerm.getParameters()[1];
				assert !arrayReads.containsKey(index) : "implement this";
				arrayReads.put(index, selectTerm);
			}
		}
		
		if (m_NewArray == null) {
			// no store
			Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (Term select : arrayReads.values()) {
				EqualityInformation eqInfo = DestructiveEqualityResolution.getEqinfo(m_Script, select, others.toArray(new Term[0]), QuantifiedFormula.EXISTS);
				if (eqInfo == null) {
					return null;
				} else {
					substitutionMapping.put(select,eqInfo.getTerm());
				}
			}
			Term result = (new SafeSubstitution(m_Script, substitutionMapping)).transform(othersT);
			if (Arrays.asList(result.getFreeVars()).contains(tv)) {
				throw new UnsupportedOperationException("not eliminated");
			} else {
				return result;
			}
		}

		
		
		
		m_Script.push(1);
		ScopedHashMap<TermVariable, Term> tv2constant = new ScopedHashMap<TermVariable, Term>();
		assertTermWithTvs(tv2constant, m_Script, othersT);
		
		UnionFind<Term> uf = new UnionFind<Term>();
		for (Term index : arrayReads.keySet()) {
			Term eqTerm = getEquivalentTerm(index, uf, tv2constant);
			uf.makeEquivalenceClass(index);
			if (eqTerm != null) {
				uf.union(index, eqTerm);
			}
		}
		Term writeIndexEqClass = getEquivalentTerm(m_WriteIndex, uf, tv2constant);
		HashSet<Term> distinctIndices = new HashSet<Term>();
		HashSet<Term> unknownIndices = new HashSet<Term>();
		divideInDistinctAndUnknown(m_WriteIndex, uf, writeIndexEqClass, distinctIndices, unknownIndices, tv2constant);
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
		
		Set<TermVariable> newAuxVars = new HashSet<TermVariable>();
		
		if (writeIndexEqClass != null) {
			for(Term writeIndexEqTerm : uf.getEquivalenceClassMembers(writeIndexEqClass)) {
				Term select = arrayReads.get(writeIndexEqTerm);
				EqualityInformation eqInfo = DestructiveEqualityResolution.getEqinfo(m_Script, select, others.toArray(new Term[0]), QuantifiedFormula.EXISTS);
				Term replacement;
				if (eqInfo == null) {
					TermVariable auxVar = writeIndexEqTerm.getTheory().createFreshTermVariable("arrayElim", select.getSort());
					newAuxVars.add(auxVar);
					replacement = auxVar;
				} else {
					replacement = eqInfo.getTerm();
				}
				substitutionMapping.put(select, replacement);
			}
		}
		Term result = (new SafeSubstitution(m_Script, substitutionMapping)).transform(othersT);
		Term newData = (new SafeSubstitution(m_Script, substitutionMapping)).transform(m_Data);
		Term t = m_Script.term("=", m_Script.term("select", m_NewArray, m_WriteIndex), newData);
		result = Util.and(m_Script, result, t);
		
		if (!newAuxVars.isEmpty()) {
			result = DestructiveEqualityResolution.derSimple(m_Script, QuantifiedFormula.EXISTS, result, newAuxVars);
			if (!newAuxVars.isEmpty()) {
				result = DestructiveEqualityResolution.updSimple(m_Script, QuantifiedFormula.EXISTS, result, newAuxVars);
				if (!newAuxVars.isEmpty()) {
					throw new UnsupportedOperationException();
				}
			}
		}
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
			Term writeIndexEqClass, HashSet<Term> distinctTerms, HashSet<Term> unknownTerms, ScopedHashMap<TermVariable, Term> tv2constant) {
		for (Term representative : uf.getAllRepresentatives()) {
			assert representative != null;
			if (representative == writeIndexEqClass) {
				// is equal, we do not want to consider
				// this equivalence class
				continue;
			}
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
	
	/**
	 * Represents Term of the form a = ("store", a', k, data)
	 */
	private static class ArrayUpdate {
		private final Term m_NewArray;
		private final Term m_Index;
		private final Term m_Data;
		private ArrayUpdate(Term newArray, Term index, Term data) {
			m_NewArray = newArray;
			m_Index = index;
			m_Data = data;
		}
		public Term getNewArray() {
			return m_NewArray;
		}
		public Term getIndex() {
			return m_Index;
		}
		public Term getData() {
			return m_Data;
		}
		public static ArrayUpdate getArrayUpdate(Term term, TermVariable tv) {
			if (term instanceof ApplicationTerm) {
				ApplicationTerm eqAppTerm = (ApplicationTerm) term;
				if (eqAppTerm.getFunction().getName().equals("=")) {
					if (eqAppTerm.getParameters().length == 2) {
						if (eqAppTerm.getParameters()[0] instanceof ApplicationTerm) {
							ApplicationTerm appTerm = (ApplicationTerm) eqAppTerm.getParameters()[0];
							if (appTerm.getFunction().getName().equals("store")) {
								if (appTerm.getParameters()[0].equals(tv)) {
									assert appTerm.getParameters().length == 3;
									ArrayUpdate au = new ArrayUpdate(
											eqAppTerm.getParameters()[1],
											appTerm.getParameters()[1],
											appTerm.getParameters()[2]);
									return au;
								}
							}
						}
						if (eqAppTerm.getParameters()[1] instanceof ApplicationTerm) {
							ApplicationTerm appTerm = (ApplicationTerm) eqAppTerm.getParameters()[1];
							if (appTerm.getFunction().getName().equals("store")) {
								if (appTerm.getParameters()[0].equals(tv)) {
									assert appTerm.getParameters().length == 3;
									ArrayUpdate au = new ArrayUpdate(
											eqAppTerm.getParameters()[0],
											appTerm.getParameters()[1],
											appTerm.getParameters()[2]);
									return au;
								}
							}
						}
					}

				}
			}
			return null;
		}
	}
}
