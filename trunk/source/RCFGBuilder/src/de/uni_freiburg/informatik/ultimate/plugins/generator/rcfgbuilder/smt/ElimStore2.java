package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.UtilExperimental;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.PartialQuantifierElimination.EqualityInformation;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;

public class ElimStore2 {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	public ElimStore2(Script script) {
		super();
		m_Script = script;
	}

	private final Script m_Script;
	private Term m_WriteIndex[];
	private Term m_Data;
	private Term m_NewArray;
	public Term elim(TermVariable oldArr, Term term) {
		assert oldArr.getSort().isArraySort();
		Term[] conjuncts = PartialQuantifierElimination.getConjuncts(term);
		HashSet<Term> others = new HashSet<Term>();
		for (Term conjunct : conjuncts) {
			if (m_NewArray == null) {
				try {
					ArrayUpdate au = new ArrayUpdate(conjunct, oldArr);
					m_WriteIndex = au.getIndex();
					m_NewArray = au.getNewArray();
					m_Data = au.getData();
					continue;
				} catch (ArrayUpdateException e) {
					// do nothing
				}
			}
			others.add(conjunct);
		}
		Term othersT = Util.and(m_Script, others.toArray(new Term[0]));
		Set<ApplicationTerm> selectTermsInData = 
				(new ApplicationTermFinder("select")).findMatchingSubterms(m_Data);
		if (m_WriteIndex == null) {
			return selectElim(oldArr, term, m_Script);
//			s_Logger.warn(new DebugMessage("not yet implemented case in "
//					+ "array quantifier elimination. Formula {0}" , term));
//			return null;
		}
		for (Term index : m_WriteIndex) {
			Set<ApplicationTerm> selectTermsInIndex = 
				(new ApplicationTermFinder("select")).findMatchingSubterms(index);
			if (!selectTermsInIndex.isEmpty()) {
				s_Logger.warn(new DebugMessage("not yet implemented case in "
						+ "array quantifier elimination. Formula {0}" , term));
				return null;
			}

		}
		Set<ApplicationTerm> selectTerms = 
				(new ApplicationTermFinder("select")).findMatchingSubterms(term);
		Map<Term[], ArrayRead> arrayReads =
				getArrayReads(oldArr, selectTerms);
		
		if (m_NewArray == null) {
			// no store
			// replace array reads by equal terms
			Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (ArrayRead ar : arrayReads.values()) {
				Term select = ar.getSelectTerm();
				EqualityInformation eqInfo = PartialQuantifierElimination.getEqinfo(
						m_Script, select, others.toArray(new Term[0]), null, QuantifiedFormula.EXISTS);
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

		
		
		HashSet<Term[]> distinctIndices = new HashSet<Term[]>();
		HashSet<Term[]> unknownIndices = new HashSet<Term[]>();
		UnionFind<Term[]> uf = new UnionFind<Term[]>();
		Term[] writeIndexEqClass;
		
		{
			m_Script.push(1);
			ScopedHashMap<TermVariable, Term> tv2constant = new ScopedHashMap<TermVariable, Term>();
			assertTermWithTvs(tv2constant, m_Script, othersT);

			Set<Term[]> indices = arrayReads.keySet();
			partitionEquivalent(tv2constant, indices, uf);
			writeIndexEqClass = getEquivalentTerm(m_WriteIndex, uf, tv2constant);

			divideInDistinctAndUnknown(m_WriteIndex, uf, writeIndexEqClass, distinctIndices, unknownIndices, tv2constant);
			m_Script.pop(1);
		}
		
		/*
		 * Add this information about inequality because it could be lost during
		 * our following substitutions. E.g. the formula
		 * a[i] = 0 && a[j] = 1
		 * implies i != j
		 * However i!=j is not implied any more if replace a[i] by 0.
		 */
		for (Term[] distinctIndex : distinctIndices) {
			others.add(m_Script.term("not", buildPairwiseEquality(distinctIndex, m_WriteIndex, m_Script)));
		}
		othersT = Util.and(m_Script, others.toArray(new Term[0]));
		

		int numberOfdisjuncts = (int) Math.pow(2,unknownIndices.size());
		Term[] disjuncts = new Term[numberOfdisjuncts];
		for (int k=0; k<numberOfdisjuncts; k++) {
			HashSet<Term[]> distinctIndicesForDisjunct = new HashSet<Term[]>(distinctIndices);
			HashSet<Term[]> equivalentIndicesForDisjunct = new HashSet<Term[]>(0);
			if (writeIndexEqClass != null) {
				equivalentIndicesForDisjunct.add(writeIndexEqClass);
			}
			Term[] conj = new Term[unknownIndices.size()+1];
			Term[][] unknownIndicesArray = unknownIndices.toArray(new Term[0][0]);
			for (int i=0; i<unknownIndicesArray.length; i++) {
				int digitOfKAtPosI = (k / (int)Math.pow(2,i)) % 2;
				assert (digitOfKAtPosI == 0 || digitOfKAtPosI == 1);
				boolean assumeEqual = (digitOfKAtPosI == 0);
				if (assumeEqual) {
					conj[i] = buildPairwiseEquality(unknownIndicesArray[i], m_WriteIndex, m_Script);
					equivalentIndicesForDisjunct.add(unknownIndicesArray[i]);
				} else {
					conj[i] = m_Script.term("not", buildPairwiseEquality(unknownIndicesArray[i], m_WriteIndex, m_Script));
					distinctIndicesForDisjunct.add(unknownIndicesArray[i]);
				}
			}
			conj[unknownIndices.size()] = buildDisjunct(oldArr, others, othersT, arrayReads,
					distinctIndicesForDisjunct, uf, equivalentIndicesForDisjunct);
			disjuncts[k] = Util.and(m_Script, conj);
		}
		return Util.or(m_Script, disjuncts);
	}

	private static Term selectElim(TermVariable oldArr, Term term, Script script) {
		Set<ApplicationTerm> selectTerms = 
				(new ApplicationTermFinder("select")).findMatchingSubterms(term);
		Term[] conjunction = PartialQuantifierElimination.getConjuncts(term);
		Map<Term[], ArrayRead> arrayReads =	getArrayReads(oldArr, selectTerms);
		ArrayRead[] all = arrayReads.values().toArray(new ArrayRead[0]);
		EqualityInformation[] eqInfos = new EqualityInformation[all.length];
		
		for (int i=0; i<all.length; i++) {
			eqInfos[i] = PartialQuantifierElimination.getEqinfo(
					script, all[i].getSelectTerm(), conjunction, null, QuantifiedFormula.EXISTS);
			if (eqInfos[i] == null) {
				return null;
			}
		}
		ArrayList<Term> additionalConjuncs = new ArrayList<Term>();
		Map<Term, Term> mapping = new HashMap<Term, Term>();
		for (int i=0; i<all.length; i++) {
			for (int j=i+1; j<all.length; j++) {
				Term indexEquality = buildPairwiseEquality(all[i].getIndex(), all[j].getIndex(), script);
				Term valueEquality = UtilExperimental.binaryEquality(script, eqInfos[i].getTerm(), eqInfos[j].getTerm());
				Term conjunct = Util.or(script, Util.not(script, indexEquality),valueEquality);
				additionalConjuncs.add(conjunct);
			}
			mapping.put(all[i].getSelectTerm(), eqInfos[i].getTerm());
		}
		SafeSubstitution subst = new SafeSubstitution(script, mapping);
		term = subst.transform(term);
		Term newConjuncts = Util.and(script, additionalConjuncs.toArray(new Term[0]));
		newConjuncts = subst.transform(newConjuncts);
		Term result = Util.and(script, term, newConjuncts);
		result = (new SimplifyDDA(script)).getSimplifiedTerm(result);
		return result;
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
			Term othersT, Map<Term[], ArrayRead> arrayReads,
			HashSet<Term[]> distinctIndices, UnionFind<Term[]> uf,
			HashSet<Term[]> equivalentIndices) {
		/*
		 * replace oldArr[i] by newArr[i] for all i that are different from the
		 * array write index
		 */
		Map<Term,Term> substitutionMapping = new HashMap<Term,Term>();
		for (Term[] distinctIndexRep : distinctIndices) {
			for (Term distTerm[] : uf.getEquivalenceClassMembers(distinctIndexRep)) {
				ApplicationTerm oldSelectTerm = arrayReads.get(distTerm).getSelectTerm();
				assert oldSelectTerm.getFunction().getName().equals("select");
				assert oldSelectTerm.getParameters().length == 2;
				assert isMultiDimensionalSelect(oldSelectTerm, oldArr, m_WriteIndex.length);
				Term newSelectTerm = buildMultiDimensionalSelect(m_NewArray, distTerm);
				substitutionMapping.put(oldSelectTerm, newSelectTerm);
			}
		}

		
		/*
		 * replace oldArr[i] by t if there is some conjunct oldArr[i] = t,
		 * otherwise replace oldArr[i] by a fresh variable
		 */
		Set<TermVariable> newAuxVars = new HashSet<TermVariable>();
		for (Term[] equivalentIndexRep : equivalentIndices) {
			for(Term[] writeIndexEqTerm : uf.getEquivalenceClassMembers(equivalentIndexRep)) {
				Term select = arrayReads.get(writeIndexEqTerm).getSelectTerm();
				EqualityInformation eqInfo = PartialQuantifierElimination.getEqinfo(
						m_Script, select, others.toArray(new Term[0]), null, QuantifiedFormula.EXISTS);
				Term replacement;
				if (eqInfo == null) {
					TermVariable auxVar = writeIndexEqTerm[0].getTheory().createFreshTermVariable("arrayElim", select.getSort());
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
		//TODO: select for store for multi dimension
		Term t = m_Script.term("=", buildMultiDimensionalSelect(m_NewArray, m_WriteIndex), newData);
		//Term t = m_Script.term("=", m_Script.term("select", m_NewArray, m_WriteIndex), newData);
		result = Util.and(m_Script, result, t);
		
		if (!newAuxVars.isEmpty()) {
			result = PartialQuantifierElimination.derSimple(m_Script, QuantifiedFormula.EXISTS, result, newAuxVars);
			if (!newAuxVars.isEmpty()) {
				result = PartialQuantifierElimination.updSimple(m_Script, QuantifiedFormula.EXISTS, result, newAuxVars);
				if (!newAuxVars.isEmpty()) {
					throw new UnsupportedOperationException();
				}
			}
		}
		return result;
	}
	
	
	/**
	 * Return true if this is a nested select on arr.
	 * Throws exception if an index contains a select.
	 */
	private boolean isMultiDimensionalSelect(Term term, Term arr, int dimension) {
		Term subterm = term;
		for (int i=0; i<dimension; i++) {
			if (!(term instanceof ApplicationTerm)) {
				return false;
			}
			ApplicationTerm subtermApp = (ApplicationTerm) subterm;
			if (!subtermApp.getFunction().getName().equals("select")) {
				return false;
			}
			subterm = subtermApp.getParameters()[0];
			Term index = subtermApp.getParameters()[1];
			Set<ApplicationTerm> selectTermsInIndex = 
					(new ApplicationTermFinder("select")).findMatchingSubterms(index);
			if (!selectTermsInIndex.isEmpty()) {
				throw new UnsupportedOperationException("select in index not supported");
			}
		}
		return subterm.equals(arr);
	}
	
	
	private Term buildMultiDimensionalSelect(Term arr, Term[] index) {
		assert index.length > 0;
		assert arr.getSort().isArraySort();
		Term result = arr;
		for (int i=0; i<index.length; i++) {
			result = m_Script.term("select", result, index[i]);
		}
		return result;
	}

	/**
	 * Build a partition such term whose equivalence can be proven are in the
	 * same equivalence class.
	 * @param tv2constant mapping from TermVariables to constants that is used
	 * for satisfiable checks.
	 */
	private UnionFind<Term[]> partitionEquivalent(
			ScopedHashMap<TermVariable, Term> tv2constant, Set<Term[]> term, UnionFind<Term[]> uf) {
		for (Term[] index : term) {
			uf.makeEquivalenceClass(index);
			Term[] eqTerm = getEquivalentTerm(index, uf, tv2constant);
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
	private static Map<Term[], ArrayRead> getArrayReads(TermVariable arrayTv,
			Set<ApplicationTerm> selectTerms) {
		Map<Term[],ArrayRead> arrayReads = new HashMap<Term[],ArrayRead>();
		for (ApplicationTerm selectTerm : selectTerms) {
			if (selectTerm.getFunction().getReturnSort().isArraySort()) {
				// this is only a select nested in some other select or store
				continue;
			}
			try {
				ArrayRead ar = new ArrayRead(selectTerm, arrayTv);
				arrayReads.put(ar.getIndex(), ar);
			} catch (ArrayReadException e) {
				// select on different array
				continue;
			}
		}
		return arrayReads;
	}
	
	/**
	 * Check if the partition uf contains a term that is equivalent to term. 
	 * @param tv2constant mapping of TermVariables to constants used in
	 * satisfiability checks (we need closed terms) 
	 */
	private Term[] getEquivalentTerm(Term[] term, UnionFind<Term[]> uf, ScopedHashMap<TermVariable, Term> tv2constant) {
		for (Term[] representative : uf.getAllRepresentatives()) {
			assert representative != null;
			assert representative.length == term.length;
			Term negated = m_Script.term("not", 
					buildPairwiseEquality(representative, term, m_Script));
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
	
	private void divideInDistinctAndUnknown(Term[] term, UnionFind<Term[]> uf, 
			Term[] writeIndexEqClass, HashSet<Term[]> distinctTerms, HashSet<Term[]> unknownTerms, ScopedHashMap<TermVariable, Term> tv2constant) {
		for (Term[] representative : uf.getAllRepresentatives()) {
			assert representative != null;
			if (representative == writeIndexEqClass) {
				// is equal, we do not want to consider
				// this equivalence class
				continue;
			}
			Term test = buildPairwiseEquality(representative, term, m_Script);
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
	
	static Term buildPairwiseEquality(Term[] first, Term[] second, Script script) {
		assert first.length == second.length;
		Term[] equivalent = new Term[first.length];
		for (int i=0; i<first.length; i++) {
			equivalent[i] = script.term("=", first[i], second[i]);
		}
		return Util.and(script, equivalent);
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
		private final TermVariable m_OldArray;
		private final TermVariable m_NewArray;
		private final Term[] m_Index;
		private final Term m_Data;
		
		private ArrayUpdate(Term term, TermVariable oldArray) throws ArrayUpdateException {
			m_OldArray = oldArray;
			int dimension = getDimension(oldArray.getSort());
			m_Index = new Term[dimension];
			if (!(term instanceof ApplicationTerm)) {
				throw new ArrayUpdateException("no ApplicationTerm");
			}
			ApplicationTerm eqAppTerm = (ApplicationTerm) term;
			if (!eqAppTerm.getFunction().getName().equals("=")) {
				throw new ArrayUpdateException("no equality");
			}
			if (!(eqAppTerm.getParameters().length == 2)) {
				throw new ArrayUpdateException("no binary equality");
			}
			Term allegedStoreTerm;
			TermVariable newArray = isArrayWithSort(eqAppTerm.getParameters()[0], oldArray.getSort());
			if (newArray != null) {
				m_NewArray = newArray;
				allegedStoreTerm = eqAppTerm.getParameters()[1];
			} else {
				newArray = isArrayWithSort(eqAppTerm.getParameters()[1], oldArray.getSort());
				if (newArray != null) {
					m_NewArray = newArray;
					allegedStoreTerm = eqAppTerm.getParameters()[0];
				} else {
					throw new ArrayUpdateException("no store term");
				}
			}
			if (!(allegedStoreTerm instanceof ApplicationTerm)) {
				throw new ArrayUpdateException("no store term");
			}
			ApplicationTerm appTerm = (ApplicationTerm) allegedStoreTerm;
			if (!appTerm.getFunction().getName().equals("store")) {
				throw new ArrayUpdateException("no store term");
			}
			assert appTerm.getParameters().length == 3;
			if (!appTerm.getParameters()[0].equals(oldArray)) {
				throw new ArrayUpdateException("different array");
			}
			m_Index[0] = appTerm.getParameters()[1];
			if (dimension == 1) {
				m_Data = appTerm.getParameters()[2];
			} else {
				if (dimension != 2) {
					throw new UnsupportedOperationException("dimension > 2 not implemented yet");
				}
				Term innnerStore = appTerm.getParameters()[2];
				if (!(innnerStore instanceof ApplicationTerm)) {
					throw new ArrayUpdateException("no ApplicationTerm");
				}
				ApplicationTerm innerStoreApp = (ApplicationTerm) innnerStore;
				if (!appTerm.getFunction().getName().equals("store")) {
					throw new ArrayUpdateException("no store term");
				}
				assert innerStoreApp.getParameters().length == 3;
				Term select = innerStoreApp.getParameters()[0];
				ApplicationTerm selectApp = (ApplicationTerm) select;
				if (!selectApp.getFunction().getName().equals("select")) {
					throw new ArrayUpdateException("no select term");
				}
				assert selectApp.getParameters().length == 2;
				if (!selectApp.getParameters()[0].equals(oldArray)) {
					throw new ArrayUpdateException("different array");
				}
				if (!selectApp.getParameters()[1].equals(m_Index[0])) {
					throw new ArrayUpdateException("different index");
				}
				m_Index[1] = innerStoreApp.getParameters()[1];
				m_Data = innerStoreApp.getParameters()[2];
			}
		}

		TermVariable isArrayWithSort(Term term, Sort sort) {
			if (term instanceof TermVariable) {
				if (term.getSort().equals(sort)) {
					return (TermVariable) term;
				} else {
					return null;
				}
			} else {
				return null;
			}
		}

		public Term getNewArray() {
			return m_NewArray;
		}
		public Term[] getIndex() {
			return m_Index;
		}
		public Term getData() {
			return m_Data;
		}
	}
	
	
	private static class ArrayUpdateException extends Exception {

		private static final long serialVersionUID = -5344050289008681972L;

		public ArrayUpdateException(String message) {
			super(message);
		}
	}
	
	
	public static int getDimension(Sort sort) {
		if (sort.isArraySort()) {
			Sort[] arg = sort.getArguments();
			assert arg.length == 2;
			return 1 + getDimension(arg[1]);
		} else {
			return 0;
		}
	}
	
	
	/**
	 * Given a (possibly nested) array a, this is a data structure for terms of
	 * the form  (select (select a i1) i2)  
	 *
	 */
	private static class ArrayRead {
		private final TermVariable m_Array;
		private final Term[] m_Index;
		private final ApplicationTerm m_SelectTerm;
		
		public ArrayRead(Term term, TermVariable tv) throws ArrayReadException {
			if (!(term instanceof ApplicationTerm)) {
				throw new ArrayReadException(false, "no ApplicationTerm");
			}
			m_SelectTerm = (ApplicationTerm) term;
			int dimension = getDimension(tv.getSort());
			m_Index = new Term[dimension];			
			for (int i = dimension-1; i>=0; i--) {
				if (!(term instanceof ApplicationTerm)) {
					throw new ArrayReadException(false, "no ApplicationTerm");
				}
				ApplicationTerm appTerm = (ApplicationTerm) term;
				if (!appTerm.getFunction().getName().equals("select")) {
					throw new ArrayReadException(false, "no select");
				}
				assert appTerm.getParameters().length == 2;
				m_Index[i] = appTerm.getParameters()[1];
				term = appTerm.getParameters()[0];
			}
			if (!tv.equals(term)) {
				throw new ArrayReadException(true, "different array");
			} else  {
				m_Array = tv;
			}
		}

		public TermVariable getArray() {
			return m_Array;
		}

		public Term[] getIndex() {
			return m_Index;
		}

		public ApplicationTerm getSelectTerm() {
			return m_SelectTerm;
		}
		
		
		
	}
	
	
	
	
	private static class ArrayReadException extends Exception {

		private static final long serialVersionUID = -628021699371967800L;
		private final boolean m_DifferentArray;

		public ArrayReadException(boolean differentArray, String message) {
			super(message);
			m_DifferentArray = differentArray;
		}
		
		public boolean reasonIsDifferentArray() {
			return m_DifferentArray;
		}
	}
	
	
	/**
	 * Only necessary for optimization where we determine which additional
	 * implied information is really needed.
	 *
	 */
	private class ImpliedReadInformation {
		Term m_ValueEquivalence;
		Term m_IndexEquivalence;
		
		public ImpliedReadInformation(ArrayRead ar1, Term equalTerm1,
				ArrayRead ar2, Term equalTerm2, 
				Term context, ScopedHashMap<TermVariable, Term> tv2constant) {
			m_IndexEquivalence = buildPairwiseEquality(ar1.getIndex(), ar2.getIndex(), m_Script);
			m_ValueEquivalence = m_Script.term("=", equalTerm1, equalTerm2);
			
			m_Script.push(1);
			tv2constant.beginScope();
			assertTermWithTvs(tv2constant, m_Script, context);
			LBool sat = m_Script.checkSat();
			tv2constant.endScope();
			m_Script.pop(1);
		}
	}
	
}
