/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate.ArrayUpdateException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate.ArrayUpdateExtractor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination.EqualityInformation;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * 
 * TODO: - elimination and output of remaining vars - nested store - storeTo and
 * storeFrom (LBE) - index equality testing - documentation
 * 
 * @author Matthias Heizmann
 * 
 */
public class ElimStore3 {

	private int m_Quantifier;
	private final Script m_Script;
	private final IFreshTermVariableConstructor m_FreshTermVariableConstructor;
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	private final static String s_FreshVariableString = "arrayElim";

	public ElimStore3(Script script, 
			IFreshTermVariableConstructor freshTermVariableConstructor, 
			IUltimateServiceProvider services) {
		super();
		m_Quantifier = QuantifiedFormula.EXISTS;
		m_Script = script;
		m_FreshTermVariableConstructor = freshTermVariableConstructor;
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(ModelCheckerUtils.sPluginID);
	}

	private MultiDimensionalStore getArrayStore(Term array, Term term) {
		List<MultiDimensionalStore> all = MultiDimensionalStore.extractArrayStoresDeep(term);
		MultiDimensionalStore result = null;
		for (MultiDimensionalStore asd : all) {
			if (asd.getArray().equals(array)) {
				if (result != null && !result.equals(asd)) {
					throw new UnsupportedOperationException("unsupported: several stores");
				} else {
					result = asd;
				}
			}
		}
		return result;
	}
	
	private ArrayUpdate getArrayUpdate(Term array, Term[] terms) {
		ArrayUpdateExtractor aue = new ArrayUpdateExtractor(m_Quantifier == QuantifiedFormula.FORALL, true, terms);
		ArrayUpdate result = null;
		for (ArrayUpdate au : aue.getArrayUpdates()) {
			if (au.getNewArray().equals(array)) {
				if (result != null && !result.equals(au)) {
					throw new UnsupportedOperationException("unsupported: several updates");
				} else {
					result = au;
				}
			}
		}
		return result;
	}

	// private ArrayStoreDef getArrayStore(Term array, Term term) {
	// Set<ApplicationTerm> storeTerms =
	// (new ApplicationTermFinder("store", true)).findMatchingSubterms(term);
	// ArrayStoreDef result = null;
	// for (Term storeTerm : storeTerms) {
	// ArrayStoreDef asd;
	// try {
	// asd = new ArrayStoreDef(storeTerm);
	// } catch (MultiDimensionalSelect.ArrayReadException e) {
	// throw new UnsupportedOperationException("unexpected store term");
	// }
	// if (asd.getArray().equals(array)) {
	// if (result != null) {
	// throw new UnsupportedOperationException("unsupported: several stores");
	// } else {
	// result = asd;
	// }
	// }
	// }
	// return result;
	// }

	public Term elim(int quantifier, TermVariable eliminatee, Term term, final Set<TermVariable> newAuxVars) {
		m_Quantifier = quantifier;
		ArrayUpdate writeInto = null;
		ArrayUpdate writtenFrom = null;
		Term[] conjuncts;
		Term othersT;

		while (true) {
			assert eliminatee.getSort().isArraySort();

			if (quantifier == QuantifiedFormula.EXISTS) {
				conjuncts = SmtUtils.getConjuncts(term);
			} else {
				assert quantifier == QuantifiedFormula.FORALL;
				conjuncts = SmtUtils.getDisjuncts(term);
			}
			if (!m_Services.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(this.getClass(),
						"eliminating quantified array variable from " + conjuncts.length + " xjuncts");
			}

			MultiDimensionalStore store = getArrayStore(eliminatee, term);
			ArrayUpdate update = getArrayUpdate(eliminatee, conjuncts);

			HashSet<Term> others = new HashSet<Term>();

			for (Term conjunct : conjuncts) {
				try {
					ArrayUpdate au = new ArrayUpdate(conjunct, quantifier == QuantifiedFormula.FORALL, false);
					if (au.getOldArray().equals(eliminatee)) {
						if (writeInto != null) {
							throw new UnsupportedOperationException("unsupported: write into several arrays");
						}
						writeInto = au;
						if (au.getNewArray().equals(eliminatee)) {
							throw new UnsupportedOperationException("unsupported: self update");
						}
					} else if (au.getNewArray().equals(eliminatee)) {
						if (writtenFrom != null) {
							throw new UnsupportedOperationException("unsupported: written from several arrayas");
						}
						writtenFrom = au;
					} else {
						others.add(conjunct);
					}
				} catch (ArrayUpdateException e) {
					others.add(conjunct);
				}
			}
			// if both are available we take the writtenFrom
			if (writtenFrom != null && writeInto != null) {
				others.add(writeInto.getArrayUpdateTerm());
				writeInto = null;
			}

			if (quantifier == QuantifiedFormula.EXISTS) {
				othersT = Util.and(m_Script, others.toArray(new Term[others.size()]));
			} else {
				assert quantifier == QuantifiedFormula.FORALL;
				othersT = Util.or(m_Script, others.toArray(new Term[others.size()]));
			}
			


			if ((store != null || update != null) && (writeInto == null && writtenFrom == null)) {
				TermVariable auxArray = m_FreshTermVariableConstructor.constructFreshTermVariable(s_FreshVariableString, eliminatee.getSort()); 
				if (store == null) {
					store = update.getMultiDimensionalStore();
				}
				Map<Term, Term> auxMap = Collections.singletonMap((Term) store.getStoreTerm(), (Term) auxArray);
				SafeSubstitution subst = new SafeSubstitution(m_Script, auxMap);
				Term auxTerm = subst.transform(term);
				Term auxVarDef = m_Script.term("=", auxArray, store.getStoreTerm());
				if (quantifier == QuantifiedFormula.EXISTS) {
					auxTerm = Util.and(m_Script, auxTerm, auxVarDef);
				} else {
					assert quantifier == QuantifiedFormula.FORALL;
					auxTerm = Util.or(m_Script, auxTerm, Util.not(m_Script, auxVarDef));
				}
				Set<TermVariable> auxAuxVars = new HashSet<TermVariable>();
				Term auxRes = elim(quantifier, eliminatee, auxTerm, newAuxVars);

				term = auxRes;
				eliminatee = auxArray;
				newAuxVars.addAll(auxAuxVars);
			} else {
				break;
			}
		}

		boolean write = (writeInto != null || writtenFrom != null);

		Script script = m_Script;
		
		Term intermediateResult = othersT;
		if (writeInto != null) {
			// if update is of form (store oldArr idx val) = newArr,
			// we replace all occurrences of (store oldArr idx val) by newArr.
			Map<Term, Term> mapping = Collections.singletonMap(
					(Term) writeInto.getMultiDimensionalStore().getStoreTerm(), (Term) writeInto.getNewArray());
			SafeSubstitution substStoreTerm = new SafeSubstitution(script, mapping);
			intermediateResult = substStoreTerm.transform(intermediateResult);
		}
		
		// Indices and corresponding values of a_elim 
		IndicesAndValues iav = new IndicesAndValues(eliminatee, conjuncts);
		SafeSubstitution subst = new SafeSubstitution(script, iav.getMapping());

		ArrayList<Term> additionalConjuncs = new ArrayList<Term>();
		intermediateResult = subst.transform(intermediateResult);
		
		if (writtenFrom == null && Arrays.asList(intermediateResult.getFreeVars()).contains(eliminatee)) {
			throw new AssertionError("var is still there " + eliminatee);
		}
		if (write) {
			Term a_heir;
			ArrayIndex idx_write;
			Term data;
			if (writeInto != null) {
				a_heir = writeInto.getNewArray();
				idx_write = writeInto.getIndex();
				data = writeInto.getValue();
			} else {
				assert writtenFrom != null;
				a_heir = writtenFrom.getOldArray();
				idx_write = writtenFrom.getIndex();
				data = writtenFrom.getValue();
			}
			additionalConjuncs.addAll(disjointIndexImpliesValueEquality(quantifier, a_heir, idx_write, iav, subst, eliminatee));
			ArrayIndex idx_writeRenamed = new ArrayIndex(SmtUtils.substitutionElementwise(idx_write, subst));
			Term dataRenamed = subst.transform(data);
			if (writeInto != null) {
				assert writeInto.getOldArray() == eliminatee : "array not eliminatee";
				// if store is of the form
				// a_heir == store(a_elim, idx_write, data)
				// construct term a_heir[idx_write] == data
				Term writtenCellHasNewValue;
				writtenCellHasNewValue = m_Script.term("=",
						SmtUtils.multiDimensionalSelect(m_Script, a_heir, idx_writeRenamed), dataRenamed);
				assert !Arrays.asList(writtenCellHasNewValue.getFreeVars()).contains(eliminatee) : "var is still there";
				additionalConjuncs.add(writtenCellHasNewValue);
			}
			
			/**
			 * Special treatment for the case that the eliminatee to which we
			 * write occurs also in a term somewhere else (which is not a
			 * select term). Maybe we can avoid this if we eliminate variables
			 * in a certain order. 
			 */
			final SafeSubstitution writtenFromSubst;
			if (writtenFrom != null) {
				Term storeRenamed = SmtUtils.multiDimensionalStore(script, a_heir, idx_writeRenamed, dataRenamed);
				Map<Term, Term> mapping = Collections.singletonMap((Term) eliminatee, storeRenamed);
				writtenFromSubst = new SafeSubstitution(script, mapping);
			} else {
				writtenFromSubst = null;
			}
			
			if (quantifier == QuantifiedFormula.EXISTS) {
				Term additionalConjuncts = Util.and(script, additionalConjuncs.toArray(new Term[additionalConjuncs.size()])); 
				intermediateResult = Util.and(script, intermediateResult, additionalConjuncts); 
			} else {
				assert quantifier == QuantifiedFormula.FORALL;
				Term additionalConjuncts = Util.or(script, SmtUtils.negateElementwise(m_Script, additionalConjuncs).toArray(new Term[additionalConjuncs.size()])); 
				intermediateResult = Util.or(script, intermediateResult, additionalConjuncts); 
			}
			
			if (writtenFromSubst != null) {
				intermediateResult = writtenFromSubst.transform(intermediateResult); 
			}
		}

		ArrayList<Term> indexValueConstraintsFromEliminatee = new ArrayList<Term>();
		{
			List<ArrayIndex> indices = new ArrayList<ArrayIndex>();
			List<Term> values = new ArrayList<Term>();
			for (int i=0; i<iav.getIndices().length; i++) {
				ArrayIndex translatedIndex = new ArrayIndex(SmtUtils.substitutionElementwise(iav.getIndices()[i], subst));
				Term translatedValue = subst.transform(iav.getValues()[i]);
				indices.add(translatedIndex);
				values.add(translatedValue);
			}
			
			
			if (writtenFrom != null) {
				assert writtenFrom.getNewArray() == eliminatee : "array not eliminatee";
				// in the writtenFrom case there is an additional index-value
				// connection on eliminatee, namely
				// that the stored data is the value at index idx_write
				ArrayIndex idx_writeRenamed = new ArrayIndex(SmtUtils.substitutionElementwise(writtenFrom.getIndex(), subst));
				Term dataRenamed = subst.transform(writtenFrom.getValue());
				indices.add(idx_writeRenamed);
				values.add(dataRenamed);
			}

			for (int i = 0; i < indices.size(); i++) {
				for (int j = i; j < indices.size(); j++) {
					Term newConjunct = SmtUtils.indexEqualityImpliesValueEquality(
							m_Script, indices.get(i), indices.get(j), values.get(i), values.get(j));
					assert !Arrays.asList(newConjunct.getFreeVars()).contains(eliminatee) : "var is still there";
					indexValueConstraintsFromEliminatee.add(newConjunct);
				}
			}
		}
		
		Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			Term newConjunctsFromSelect = Util.and(m_Script, indexValueConstraintsFromEliminatee.toArray(new Term[indexValueConstraintsFromEliminatee.size()]));
			result = Util.and(script, intermediateResult, newConjunctsFromSelect);
		} else {
			assert quantifier == QuantifiedFormula.FORALL;
			Term newConjunctsFromSelect = Util.or(m_Script, SmtUtils.negateElementwise(m_Script, indexValueConstraintsFromEliminatee).toArray(new Term[indexValueConstraintsFromEliminatee.size()]));
			result = Util.or(script, intermediateResult, newConjunctsFromSelect);
		}

		result = SmtUtils.simplify(script, result, m_Services);
		newAuxVars.addAll(iav.getNewAuxVars());

		return result;
	}

	
	/**
	 * let idx_write be the index to which the store writes
	 * let k_1,...,k_n be indices of the eliminated array
	 * let v_1,...,v_n be terms that are equivalent to the corresponding
	 * values of the eliminated array (i.e. v_i is equivalent to a_elim[k_i]
	 * add for each i the conjunct
	 * (idx_write != k_i) ==> (v_i == a_heir[i])
	 * 
	 * Says that for each index that is different from the write index the
	 * arrayCells of a_heir have the same values than the arrayCells of
	 * a_elim
	 * @param subst 
	 * @param eliminatee 
	 */
	private ArrayList<Term> disjointIndexImpliesValueEquality(int quantifier,
			Term a_heir, ArrayIndex idx_write, IndicesAndValues iav, SafeSubstitution subst, TermVariable eliminatee) {
		ArrayList<Term> result = new ArrayList<Term>();
		for (int i = 0; i < iav.getIndices().length; i++) {
			// select term that represents the array cell a[]
			Term selectOnHeir = SmtUtils.multiDimensionalSelect(m_Script, a_heir, iav.getIndices()[i]);
			IndexValueConnection ivc = new IndexValueConnection(iav.getIndices()[i], idx_write,
					iav.getValues()[i], selectOnHeir, false);
			Term conjunct = ivc.getTerm();
			conjunct = subst.transform(conjunct);
			result.add(conjunct);
			assert !Arrays.asList(conjunct.getFreeVars()).contains(eliminatee) : "var is still there";
			if (ivc.indexInequality() && !ivc.valueEquality()) {
				assert !ivc.valueInequality() : "term would be false!";
				// case where we have valueEquality hat is not true
				// do something useful...
				// e.g., mark newSelect as occurring or mark auxVar as
				// equal to something
			}
		}
		return result;
	}

//	public static Term indexValueConnections(ArrayIndex ourIndex, Term ourValue, ArrayIndex[] othersIndices,
//			Term[] othersValues, int othersPosition, Script script, int quantifier) {
//		assert othersIndices.length == othersValues.length;
//		ArrayList<Term> additionalConjuncs = new ArrayList<Term>();
//		for (int i = othersPosition; i < othersIndices.length; i++) {
//			ArrayIndex othersIndex = othersIndices[i];
//			assert ourIndex.size() == othersIndex.size();
//			Term indexEquality = Util.and(script, buildPairwiseEquality(ourIndex, othersIndices[i], null, script));
//			Term valueEquality = SmtUtils.binaryEquality(script, ourValue, othersValues[i]);
//			Term conjunct = Util.or(script, Util.not(script, indexEquality), valueEquality);
//			if (quantifier == QuantifiedFormula.EXISTS) {
//				additionalConjuncs.add(conjunct);
//			} else {
//				assert quantifier == QuantifiedFormula.FORALL;
//				additionalConjuncs.add(Util.not(script, conjunct));
//			}
//		}
//		Term result;
//		if (quantifier == QuantifiedFormula.EXISTS) {
//			result = Util.and(script, additionalConjuncs.toArray(new Term[additionalConjuncs.size()]));
//		} else {
//			assert quantifier == QuantifiedFormula.FORALL;
//			result = Util.or(script, additionalConjuncs.toArray(new Term[additionalConjuncs.size()]));
//		}
//
//		
//
//		return result;
//	}
	
	


	/**
	 * Given an array a, find all multi-dimensional selects on this array.
	 * For each of them, try to obtain an representation of that value in which
	 * a does not occur. If not such representation exists, add a new auxiliary
	 * variable that represents that value.
	 *
	 */
	private class IndicesAndValues {
		private final Term[] m_SelectTerm;
		private final ArrayIndex[] m_Indices;
		private final Term m_Values[];
		private final Set<TermVariable> m_NewAuxVars;
		private final Map<Term, Term> m_SelectTerm2Value = new HashMap<Term, Term>();

		public IndicesAndValues(TermVariable array, Term[] conjuncts) {
			Set<MultiDimensionalSelect> set = new HashSet<MultiDimensionalSelect>();
			for (Term conjunct : conjuncts) {
				for (MultiDimensionalSelect mdSelect : MultiDimensionalSelect.extractSelectDeep(conjunct, false)) {
					if (mdSelect.getArray().equals(array)) {
						set.add(mdSelect);
					}
				}
			}
			MultiDimensionalSelect[] arrayReads = set.toArray(new MultiDimensionalSelect[set.size()]);
			m_SelectTerm = new Term[arrayReads.length];
			m_Indices = new ArrayIndex[arrayReads.length];
			m_Values = new Term[arrayReads.length];
			m_NewAuxVars = new HashSet<TermVariable>();
			for (int i = 0; i < arrayReads.length; i++) {
				m_SelectTerm[i] = arrayReads[i].getSelectTerm();
				m_Indices[i] = arrayReads[i].getIndex();
				EqualityInformation eqInfo = EqualityInformation.getEqinfo(m_Script,
						arrayReads[i].getSelectTerm(), conjuncts, array, m_Quantifier, m_Logger);
				if (eqInfo == null) {
					Term select = arrayReads[i].getSelectTerm();
					TermVariable auxVar = m_FreshTermVariableConstructor.
							constructFreshTermVariable(s_FreshVariableString, select.getSort());
					m_NewAuxVars.add(auxVar);
					m_Values[i] = auxVar;
				} else {
					m_Values[i] = eqInfo.getTerm();
				}
				m_SelectTerm2Value.put(m_SelectTerm[i], m_Values[i]);
			}
		}

		public Term[] getSelectTerm() {
			return m_SelectTerm;
		}

		public ArrayIndex[] getIndices() {
			return m_Indices;
		}

		public Term[] getValues() {
			return m_Values;
		}

		public Set<TermVariable> getNewAuxVars() {
			return m_NewAuxVars;
		}

		public Map<Term, Term> getMapping() {
			return m_SelectTerm2Value;
		}
	}

	/**
	 * Class that constructs the term 
	 *     (fstIndex == sndIndex) ==> (fstValue == sndValue)
	 * if selectConnection is true and the term
	 *     (fstIndex != sndIndex) ==> (fstValue == sndValue)
	 * if selectConnection is false.
	 *
	 */
	private class IndexValueConnection {
		private final ArrayIndex m_fstIndex;
		private final ArrayIndex m_sndIndex;
		private final Term m_fstValue;
		private final Term m_sndValue;
		private final boolean m_SelectConnection;
		private final Term m_IndexEquality;
		private final Term m_ValueEquality;

		public IndexValueConnection(ArrayIndex fstIndex, ArrayIndex sndIndex, Term fstValue, Term sndValue,
				boolean selectConnection) {
			m_fstIndex = fstIndex;
			m_sndIndex = sndIndex;
			m_fstValue = fstValue;
			m_sndValue = sndValue;
			m_SelectConnection = selectConnection;
			m_IndexEquality = Util.and(m_Script, SmtUtils.pairwiseEquality(m_Script, fstIndex, sndIndex));
			m_ValueEquality = SmtUtils.binaryEquality(m_Script, fstValue, sndValue);
		}

		/**
		 * Is equality of both indices already implied by context?
		 */
		public boolean indexEquality() {
			return m_IndexEquality.equals(m_Script.term("true"));
		}

		/**
		 * Is inequality of both indices already implied by context?
		 */
		public boolean indexInequality() {
			return m_IndexEquality.equals(m_Script.term("false"));
		}

		/**
		 * Is equality of both values already implied by context?
		 */
		public boolean valueEquality() {
			return m_ValueEquality.equals(m_Script.term("true"));
		}

		/**
		 * Is inequality of both values already implied by context?
		 */
		public boolean valueInequality() {
			return m_ValueEquality.equals(m_Script.term("false"));
		}

		public Term getTerm() {
			Term indexTerm = m_IndexEquality;
			if (m_SelectConnection) {
				indexTerm = Util.not(m_Script, indexTerm);
			}
			return Util.or(m_Script, indexTerm, m_ValueEquality);

		}
	}

	/**
	 * Return true if this is a nested select on arr. Throws exception if an
	 * index contains a select.
	 */
	private boolean isMultiDimensionalSelect(Term term, Term arr, int dimension) {
		Term subterm = term;
		for (int i = 0; i < dimension; i++) {
			if (!(term instanceof ApplicationTerm)) {
				return false;
			}
			ApplicationTerm subtermApp = (ApplicationTerm) subterm;
			if (!subtermApp.getFunction().getName().equals("select")) {
				return false;
			}
			subterm = subtermApp.getParameters()[0];
			Term index = subtermApp.getParameters()[1];
			Set<ApplicationTerm> selectTermsInIndex = (new ApplicationTermFinder("select", true))
					.findMatchingSubterms(index);
			if (!selectTermsInIndex.isEmpty()) {
				throw new UnsupportedOperationException("select in index not supported");
			}
		}
		return subterm.equals(arr);
	}

	// /**
	// * Return all selectTerms that read from the array given by arrayTv.
	// * @param selectTerms a[i],
	// * @return
	// */
	// private static Map<Term[], MultiDimensionalSelect> getArrayReads(
	// TermVariable arrayTv,
	// Set<ApplicationTerm> selectTerms) {
	// Map<Term[],MultiDimensionalSelect> index2mdSelect =
	// new HashMap<Term[],MultiDimensionalSelect>();
	// for (ApplicationTerm selectTerm : selectTerms) {
	// if (selectTerm.getFunction().getReturnSort().isArraySort()) {
	// // this is only a select nested in some other select or store
	// continue;
	// }
	// MultiDimensionalSelect ar = new MultiDimensionalSelect(selectTerm);
	// if (ar.getArray() == arrayTv) {
	// index2mdSelect.put(ar.getIndex(), ar);
	// } else {
	// // select on different array
	// continue;
	// }
	// }
	// return index2mdSelect;
	// }

	/**
	 * Given two lists of terms and a subsitution subst return the following
	 * conjunctions subst(first_1) == subst(second_1), ... ,subst(first_n) ==
	 * subst(second_n) if subst is null we use the identity function.
	 */
	private static Term[] buildPairwiseEquality(ArrayIndex first, ArrayIndex second, SafeSubstitution subst, Script script) {
		assert first.size() == second.size();
		Term[] equivalent = new Term[first.size()];
		for (int i = 0; i < first.size(); i++) {
			Term firstTerm, secondTerm;
			if (subst == null) {
				firstTerm = first.get(i);
				secondTerm = second.get(i);
			} else {
				firstTerm = subst.transform(first.get(i));
				secondTerm = subst.transform(second.get(i));
			}
			equivalent[i] = SmtUtils.binaryEquality(script, firstTerm, secondTerm);
		}
		return equivalent;
	}

	/**
	 * assert term, replace TermVariable by constants in advance, replace by
	 * constants defined by mapping, if no constant defined by mapping declare
	 * constant and add to mapping
	 */
	private void assertTermWithTvs(Map<TermVariable, Term> mapping, Script script, Term term) {
		for (TermVariable tv : term.getFreeVars()) {
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

	// public static int getDimension(Sort sort) {
	// if (sort.isArraySort()) {
	// Sort[] arg = sort.getArguments();
	// assert arg.length == 2;
	// return 1 + getDimension(arg[1]);
	// } else {
	// return 0;
	// }
	// }

}
