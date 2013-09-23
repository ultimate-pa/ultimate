package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.Arrays;
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
	public Term elim(TermVariable oldArr, Term term) {
		assert oldArr.getSort().isArraySort();
		Term[] conjuncts = DestructiveEqualityResolution.getConjuncts(term);
		HashSet<Term> others = new HashSet<Term>();
		for (Term conjunct : conjuncts) {
			if (m_NewArray == null) {
				ArrayUpdate au = ArrayUpdate.getArrayUpdate(conjunct, oldArr);
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
		Set<ApplicationTerm> selectTerms = 
				(new ApplicationTermFinder("select")).findMatchingSubterms(term);
		Map<Term, ApplicationTerm> arrayReads =
				getArrayReads(oldArr,	selectTerms);
		
		if (m_NewArray == null) {
			// no store
			// replace array reads by equal terms
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
			if (Arrays.asList(result.getFreeVars()).contains(oldArr)) {
				throw new UnsupportedOperationException("not eliminated");
			} else {
				return result;
			}
		}

		
		
		HashSet<Term> distinctIndices = new HashSet<Term>();
		HashSet<Term> unknownIndices = new HashSet<Term>();
		UnionFind<Term> uf = new UnionFind<Term>();
		Term writeIndexEqClass;
		
		{
			m_Script.push(1);
			ScopedHashMap<TermVariable, Term> tv2constant = new ScopedHashMap<TermVariable, Term>();
			assertTermWithTvs(tv2constant, m_Script, othersT);

			Set<Term> indices = arrayReads.keySet();
			partitionEquivalent(tv2constant, indices, uf);
			writeIndexEqClass = getEquivalentTerm(m_WriteIndex, uf, tv2constant);

			divideInDistinctAndUnknown(m_WriteIndex, uf, writeIndexEqClass, distinctIndices, unknownIndices, tv2constant);
			m_Script.pop(1);
		}
		

		int numberOfdisjuncts = (int) Math.pow(2,unknownIndices.size());
		Term[] disjuncts = new Term[numberOfdisjuncts];
		for (int k=0; k<numberOfdisjuncts; k++) {
			HashSet<Term> distinctIndicesForDisjunct = new HashSet<Term>(distinctIndices);
			HashSet<Term> equivalentIndicesForDisjunct = new HashSet<Term>(0);
			if (writeIndexEqClass != null) {
				equivalentIndicesForDisjunct.add(writeIndexEqClass);
			}
			Term[] conj = new Term[unknownIndices.size()+1];
			Term[] unknownIndicesArray = unknownIndices.toArray(new Term[0]);
			for (int i=0; i<unknownIndicesArray.length; i++) {
				int digitOfKAtPosI = (k / (int)Math.pow(2,i)) % 2;
				assert (digitOfKAtPosI == 0 || digitOfKAtPosI == 1);
				boolean assumeEqual = (digitOfKAtPosI == 0);
				if (assumeEqual) {
					conj[i] = m_Script.term("=", unknownIndicesArray[i], m_WriteIndex);
					equivalentIndicesForDisjunct.add(unknownIndicesArray[i]);
				} else {
					conj[i] = m_Script.term("not", m_Script.term("=", unknownIndicesArray[i], m_WriteIndex));
					distinctIndicesForDisjunct.add(unknownIndicesArray[i]);
				}
			}
			conj[unknownIndices.size()] = buildDisjunct(oldArr, others, othersT, arrayReads,
					distinctIndicesForDisjunct, uf, equivalentIndicesForDisjunct);
			disjuncts[k] = Util.and(m_Script, conj);
		}
		return Util.or(m_Script, disjuncts);
	}

	/**
	 * @param oldArr
	 * @param others
	 * @param othersT
	 * @param arrayReads
	 * @param distinctIndices
	 * @param uf
	 * @param writeIndexEqClass
	 * @return
	 */
	private Term buildDisjunct(TermVariable oldArr, HashSet<Term> others,
			Term othersT, Map<Term, ApplicationTerm> arrayReads,
			HashSet<Term> distinctIndices, UnionFind<Term> uf,
			HashSet<Term> equivalentIndices) {
		/*
		 * replace oldArr[i] by newArr[i] for all i that are different from the
		 * array write index
		 */
		Map<Term,Term> substitutionMapping = new HashMap<Term,Term>();
		for (Term distinctIndexRep : distinctIndices) {
			for (Term distTerm : uf.getEquivalenceClassMembers(distinctIndexRep)) {
				ApplicationTerm oldSelectTerm = arrayReads.get(distTerm);
				assert oldSelectTerm.getFunction().getName().equals("select");
				assert oldSelectTerm.getParameters().length == 2;
				assert oldSelectTerm.getParameters()[0] == oldArr;
				Set<ApplicationTerm> selectTermsInIndex = 
						(new ApplicationTermFinder("select")).findMatchingSubterms(oldSelectTerm.getParameters()[0]);
				if (!selectTermsInIndex.isEmpty()) {
					throw new UnsupportedOperationException("select in index not supported");
				}
				Term newSelectTerm = m_Script.term("select", m_NewArray, oldSelectTerm.getParameters()[1]);
				substitutionMapping.put(oldSelectTerm, newSelectTerm);
			}
		}

		
		/*
		 * replace oldArr[i] by t if there is some conjunct oldArr[i] = t,
		 * otherwise replace oldArr[i] by a fresh variable
		 */
		Set<TermVariable> newAuxVars = new HashSet<TermVariable>();
		for (Term equivalentIndexRep : equivalentIndices) {
			for(Term writeIndexEqTerm : uf.getEquivalenceClassMembers(equivalentIndexRep)) {
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
		return result;
	}

	/**
	 * Build a partition such term whose equivalence can be proven are in the
	 * same equivalence class.
	 * @param tv2constant mapping from TermVariables to constants that is used
	 * for satisfiable checks.
	 */
	private UnionFind<Term> partitionEquivalent(
			ScopedHashMap<TermVariable, Term> tv2constant, Set<Term> term, UnionFind<Term> uf) {
		for (Term index : term) {
			uf.makeEquivalenceClass(index);
			Term eqTerm = getEquivalentTerm(index, uf, tv2constant);
			if (eqTerm != null) {
				uf.union(index, eqTerm);
			}
		}
		return uf;
	}

	/**
	 * Return all selectTerms that read from the array given by arrayTv.
	 * @param selectTerms a[i], 
	 * @return
	 */
	private Map<Term, ApplicationTerm> getArrayReads(TermVariable arrayTv,
			Set<ApplicationTerm> selectTerms) {
		Map<Term,ApplicationTerm> arrayReads = new HashMap<Term,ApplicationTerm>();
		for (ApplicationTerm selectTerm : selectTerms) {
			if (selectTerm.getParameters()[0].equals(arrayTv)) {
				Term index = selectTerm.getParameters()[1];
				if (arrayReads.containsKey(index)) {
					throw new UnsupportedOperationException("several array" +
							" reads at the same index are not supported at the moment");
				}
				arrayReads.put(index, selectTerm);
			}
		}
		return arrayReads;
	}
	
	/**
	 * Check if the partition uf contains a term that is equivalent to term. 
	 * @param tv2constant mapping of TermVariables to constants used in
	 * satisfiability checks (we need closed terms) 
	 */
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
