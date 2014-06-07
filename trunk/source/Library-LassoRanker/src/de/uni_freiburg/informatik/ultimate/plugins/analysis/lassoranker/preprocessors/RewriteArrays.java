/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.RankVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.VarCollector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.ElimStore3.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.ElimStore3.ArrayUpdateException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.MultiDimensionalStore.ArrayStoreException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.SmtUtils.MultiDimensionalArraySort;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.normalForms.Dnf;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;


/**
 * Replace term with arrays by term without arrays by introducing replacement
 * variables for all "important" array values and equalities that state the
 * constraints between array indices and array values (resp. their replacement
 * variables). 
 * 
 * 
 * @author Matthias Heizmann
 */
public class RewriteArrays implements PreProcessor {
	private static final String s_RepInPostfix  = "_in_array";
	private static final String s_RepOutPostfix = "_out_array";
	private static final String s_AuxArray = "auxArray";
	
	/**
	 * The script used to transform the formula
	 */
	private Script m_Script;
	
	/**
	 * Collection of all generated replacement variables and the terms
	 * that they replace.
	 * These variables are *not* added to in- or outVars.
	 */
	private final Map<TermVariable, Term> m_repVars;
	
	/**
	 * The replacement terms for the replacement variables for the formula.
	 * These terms will be set in conjunction with the whole formula.
	 */
	private final Collection<Term> m_repTerms;
	
	/**
	 * For generating replacement variables
	 */
	private final VarCollector m_VarCollector;
	
	/**
	 * Use assert statement to check if result is equivalent to the conjunction
	 * of input term and definition of replacement variables. 
	 */
	private static final boolean s_CheckResult = true;
	/**
	 * Use assert statement to check if the input is equivalent to the formula
	 * that is obtained by existentially quantifying each replacement variable
	 * in the result term.
	 */
	private static final boolean s_CheckResultWithQuantifiers = false;
	
	
	private HashRelation<TermVariable, List<Term>> m_Array2Indices;
	List<ArrayUpdate>[] m_ArrayUpdates;
	List<MultiDimensionalSelect>[] m_ArrayReads;
	ArrayGenealogy[] m_ArrayGenealogy;
	private Map<TermVariable, Map<List<Term>, TermVariable>> m_ArrayInstance2Index2CellVariable;
	private Term[] sunnf;
	private List<ArrayEquality>[] m_ArrayEqualities;
	
	public RewriteArrays(VarCollector rankVarCollector) {
		m_VarCollector = rankVarCollector;
		m_repVars = new LinkedHashMap<TermVariable, Term>();
		m_repTerms = new ArrayList<Term>();
	}
	
	@Override
	public String getDescription() {
		return "Removes arrays by introducing new variables for each " +
				"relevant array cell";
	}
	
	@Override
	public Term process(Script script, Term term) {
		m_Script = script;
		Term dnf = (new Dnf(script)).transform(term);
		Term[] disjuncts = PartialQuantifierElimination.getDisjuncts(dnf);
		sunnf = new Term[disjuncts.length];
		m_ArrayUpdates = new List[disjuncts.length];
		m_ArrayReads = new List[disjuncts.length];
		m_ArrayEqualities = new List[disjuncts.length];
		m_ArrayGenealogy = new ArrayGenealogy[disjuncts.length];
		for (int i=0; i<disjuncts.length; i++) {
			SingleUpdateNormalFormTransformer sunnft = new SingleUpdateNormalFormTransformer(disjuncts[i]);
			m_ArrayUpdates[i] = sunnft.getArrayUpdates();
			sunnf[i] = sunnft.getTerm();
			m_ArrayReads[i] = MultiDimensionalSelect.extractSelectDeep(sunnf[i], true); 
			m_ArrayEqualities[i] = extractArrayEqualities(sunnf[i]);
			m_ArrayGenealogy[i] = new ArrayGenealogy(m_ArrayUpdates[i], m_ArrayReads[i]);
		}
		
		new IndexCollector();
		CellVariableBuilder cvb = new CellVariableBuilder();
		m_ArrayInstance2Index2CellVariable = cvb.getArrayInstance2Index2CellVariable();
		Term indexValueConstraints = buildIndexValueConstraints();
		
		Term[] arrayUpdateConstraints = new Term[sunnf.length]; 
		for (int i=0; i<disjuncts.length; i++) {
			arrayUpdateConstraints[i] = buildArrayUpdateConstraints(m_ArrayUpdates[i]); 
		}
		Term[] disjunctsWithUpdateConstraints = new Term[sunnf.length];
		for (int i=0; i<disjunctsWithUpdateConstraints.length; i++) {
			disjunctsWithUpdateConstraints[i] = Util.and(m_Script, sunnf[i], arrayUpdateConstraints[i]);
		}
		Term resultDisjuntion = Util.or(m_Script, disjunctsWithUpdateConstraints);
		Term result = Util.and(m_Script, resultDisjuntion, indexValueConstraints);
		
		Term removed = removeArrayUpdateAndArrayReads(result);
		m_VarCollector.addAuxVars(cvb.getAuxVars());

		
//			assert !s_CheckResult || !isIncorrect(term, result, repTerm) 
//					: "rewrite division unsound";
//			assert !s_CheckResultWithQuantifiers
//					||	!isIncorrectWithQuantifiers(term, result, repTerm) 
//					: "rewrite division unsound";
		isArrayFree(removed);
		return removed;
	}
	
	
	
	
	/**
	 * Return true if we were able to prove that the result is incorrect.
	 * For this check we add to the input term the definition of the replacement
	 * variables.
	 */
	private boolean isIncorrect(Term input, Term result, Term repTerm) {
		Term inputWithDefinitions = m_Script.term("and", input, repTerm);
		return LBool.SAT == Util.checkSat(m_Script,
				m_Script.term("distinct",  inputWithDefinitions, result));
	}
	
	/**
	 * Return true if we were able to prove that the result is incorrect.
	 * For this check we existentially quantify replacement variables in the
	 * result term.
	 */
	private boolean isIncorrectWithQuantifiers(Term input, Term result,
			Term repTerm) {
		Term quantified;
		if (m_repVars.size() > 0) {
			quantified = m_Script.quantifier(Script.EXISTS,
					m_repVars.keySet().toArray(new TermVariable[0]), result);
		} else {
			quantified = m_Script.term("true");
		}
		return Util.checkSat(m_Script, m_Script.term("distinct", 
				input, quantified)) == LBool.SAT;
	}
	

	
	private List<MultiDimensionalStore> extractArrayStores(Term term) {
		List<MultiDimensionalStore> foundInThisIteration = new ArrayList<MultiDimensionalStore>();
		Set<ApplicationTerm> storeTerms = 
				(new ApplicationTermFinder("store", false)).findMatchingSubterms(term);
		for (Term storeTerm : storeTerms) {
			MultiDimensionalStore asd;
			try {
				asd = new MultiDimensionalStore(storeTerm);
			} catch (ArrayStoreException e) {
				throw new UnsupportedOperationException("unexpected store term");
			}
			foundInThisIteration.add(asd);
		}
		List<MultiDimensionalStore> result = new LinkedList<MultiDimensionalStore>();
		while (!foundInThisIteration.isEmpty()) {
			result.addAll(0, foundInThisIteration);
			List<MultiDimensionalStore> foundInLastIteration = foundInThisIteration;
			foundInThisIteration = new ArrayList<MultiDimensionalStore>();
			for (MultiDimensionalStore asd : foundInLastIteration) {
				storeTerms = 
						(new ApplicationTermFinder("store", false)).findMatchingSubterms(asd.getArray());
				for (Term storeTerm : storeTerms) {
					MultiDimensionalStore newAsd;
					try {
						newAsd = new MultiDimensionalStore(storeTerm);
					} catch (ArrayStoreException e) {
						throw new UnsupportedOperationException("unexpected store term");
					}
					foundInThisIteration.add(newAsd);
				}
			}
		}
		return result;
	}
	
	
	private class ArrayGenealogy {
		Map<TermVariable, TermVariable> m_Instance2OriginalGeneration = new HashMap<TermVariable, TermVariable>();
		
		/**
		 * If array a2 is defined as a2 = ("store", a1, index, value) we call
		 * a1 the parent generation of a2.  
		 */
		Map<TermVariable, TermVariable> m_ParentGeneration = new HashMap<TermVariable, TermVariable>();
		
		ArrayGenealogy(List<ArrayUpdate> arrayUpdates, List<MultiDimensionalSelect> arrayReads) {
			for (ArrayUpdate au : arrayUpdates) {
				m_ParentGeneration.put(au.getNewArray(), au.getOldArray());
			}
			for (TermVariable tv : m_ParentGeneration.keySet()) {
				TermVariable fg = getFirstGeneration(tv);
				m_Instance2OriginalGeneration.put(tv, fg);
				// we add first generation several times, probably
				// less expensive than checking if already inserted
				m_Instance2OriginalGeneration.put(fg, fg);
			}
			for (MultiDimensionalSelect ar : arrayReads) {
				if (m_Instance2OriginalGeneration.get(ar.getArray()) == null) {
					m_Instance2OriginalGeneration.put((TermVariable)ar.getArray(), (TermVariable)ar.getArray());
				}
			}
		}
		
		private TermVariable getFirstGeneration(TermVariable tv) {
			TermVariable parent = m_ParentGeneration.get(tv);
			if (parent == null) {
				return tv;
			} else {
				return getFirstGeneration(parent);
			}
		}
		
		public TermVariable getProgenitor(TermVariable tv) {
			return m_Instance2OriginalGeneration.get(tv);
		}
		
		public Set<TermVariable> getInstances() {
			return m_Instance2OriginalGeneration.keySet();
		}
	}
	
	private class SingleUpdateNormalFormTransformer {

		List<ArrayUpdate> m_ArrayUpdates;
		
		Term m_Term;

		public SingleUpdateNormalFormTransformer(Term term) {
			super();
			m_Term = term;
			doTransform();
		}
		
		private void doTransform() {
			boolean m_EachArrayHasSingleUpdate = false;
			while(!m_EachArrayHasSingleUpdate) {
				Object result = eachArrayHasSingleUpdate();
				if (result instanceof MultiDimensionalStore) {
					update((MultiDimensionalStore) result);
				} else {
					m_EachArrayHasSingleUpdate = true;
					m_ArrayUpdates = (List<ArrayUpdate>) result;
				}
			}
		}
		
		private Object eachArrayHasSingleUpdate() {
			List<ArrayUpdate> arrayUpdates = new ArrayList<ArrayUpdate>();
			List<MultiDimensionalStore> arrayStores = extractArrayStores(m_Term);
			for (MultiDimensionalStore arrayStore : arrayStores) {
				ArrayUpdate au;
				try {
					au = findCorrespondingArrayUpdate(m_Term, arrayStore);
				} catch (ArrayUpdateException e) {
					continue;
				}
				arrayUpdates.add(au);
				if (au == null) {
					return arrayStore;
				}
			}
			assert (arrayStores.size() == arrayUpdates.size());
			return arrayUpdates;
		}
		
		private void update(MultiDimensionalStore arraryStore) {
			Term oldArray = arraryStore.getArray();
			String name = oldArray.toString() + s_AuxArray; 
			TermVariable auxArray = 
					m_VarCollector.getFactory().getNewTermVariable(name, oldArray.getSort());
			Map<Term, Term> substitutionMapping = 
					Collections.singletonMap((Term) arraryStore.getStoreTerm(), (Term) auxArray);
			Term newTerm = (new SafeSubstitution(m_Script, substitutionMapping)).transform(m_Term);
			newTerm = m_Script.term("and", newTerm, m_Script.term("=", auxArray, arraryStore.getStoreTerm()));
			m_Term = newTerm;
		}

		private ArrayUpdate findCorrespondingArrayUpdate(Term term, MultiDimensionalStore asd) throws ArrayUpdateException {
			Set<ApplicationTerm> equalities = 
					(new ApplicationTermFinder("=", true)).findMatchingSubterms(term);
			for (ApplicationTerm equality : equalities) {
				Term[] params = equality.getParameters();
				if (params.length > 2) {
					throw new UnsupportedOperationException("only binary equalities at the moment");
				}
				if (params[1] == asd.getStoreTerm() || params[1] == asd.getStoreTerm()) {
					try {
						return new ArrayUpdate(equality);
					} catch (ArrayUpdateException e) {
						if (e.getMessage().equals("no term variable")) {
							throw e;
						} else {
							throw new AssertionError();
						}
					}
				}
			}
			return null;
		}

		public List<ArrayUpdate> getArrayUpdates() {
			return Collections.unmodifiableList(m_ArrayUpdates);
		}



		public Term getTerm() {
			return m_Term;
		}
	}
	
	private List<ArrayEquality> extractArrayEqualities(Term term) {
		Set<ApplicationTerm> equalityTerms = 
				(new ApplicationTermFinder("=", true)).findMatchingSubterms(term);
		List<ArrayEquality> arrayEqualities = new ArrayList<ArrayEquality>();
		for (ApplicationTerm equalityTerm : equalityTerms) {
				try {
					ArrayEquality ae = new ArrayEquality(equalityTerm);
					arrayEqualities.add(ae);
				} catch (ArrayEqualityException e) {
					// do not add
				}
			}
		return arrayEqualities;
	}
	
	
	private class IndexCollector {
		
		public IndexCollector() {
			m_Array2Indices = new HashRelation<TermVariable, List<Term>>();
			for (int i=0; i<sunnf.length; i++) {
				for(ArrayUpdate au : m_ArrayUpdates[i]) {
					TermVariable firstGeneration = m_ArrayGenealogy[i].getProgenitor(au.getOldArray());
					Term[] index = au.getIndex();
					m_Array2Indices.addPair(firstGeneration, Arrays.asList(index));
				}
				for (MultiDimensionalSelect ar : m_ArrayReads[i]) {
					TermVariable firstGeneration = m_ArrayGenealogy[i].getProgenitor((TermVariable) ar.getArray());
					Term[] index = ar.getIndex();
					m_Array2Indices.addPair(firstGeneration, Arrays.asList(index));
				}
			}
		}
	}
	

	
	private class CellVariableBuilder {
		private Map<TermVariable, Map<List<Term>, TermVariable>> m_ArrayInstance2Index2CellVariable;
		private Map<TermVariable, Map<List<Term>, ReplacementVar>> m_Array2Index2RepVar;
		private Set<TermVariable> m_AuxVars = new HashSet<TermVariable>();
		
		
		
		public CellVariableBuilder() {
			m_ArrayInstance2Index2CellVariable = new HashMap<TermVariable, Map<List<Term>,TermVariable>>();
			m_Array2Index2RepVar = new HashMap<TermVariable, Map<List<Term>,ReplacementVar>>();
			dotSomething();
		}

		/**
		 * Returns a getOrConstructReplacementVar that will represent the array
		 * cell array[index].
		 */
		private ReplacementVar getOrConstructReplacementVar(TermVariable array, List<Term> index) {
			List<Term> translatedIndex = Arrays.asList(translateTermVariablesToDefinitions(index.toArray(new Term[0])));
			Map<List<Term>, ReplacementVar> index2repVar = m_Array2Index2RepVar.get(array);
			if (index2repVar == null) {
				index2repVar = new HashMap<List<Term>, ReplacementVar>();
				m_Array2Index2RepVar.put(array, index2repVar);
			}
			ReplacementVar repVar = index2repVar.get(translatedIndex);
			if (repVar == null) {
				repVar = constructReplacementVar(array, translatedIndex);
				index2repVar.put(translatedIndex, repVar);
			}
			return repVar;
		}
		
		private Term getDefinition(TermVariable tv) {
			RankVar rv = m_VarCollector.getInVarsReverseMapping().get(tv);
			if (rv == null) {
				rv = m_VarCollector.getOutVarsReverseMapping().get(tv);
			}
			if (rv == null) {
				throw new AssertionError();
			}
			return rv.getDefinition();
		}
		
		private Term[] translateTermVariablesToDefinitions(Term... terms) {
			Term[] result = new Term[terms.length];
			for (int i=0; i<terms.length; i++) {
				Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
				for (TermVariable tv : terms[i].getFreeVars()) {
					Term definition = getDefinition(tv);
					substitutionMapping.put(tv, definition);
				}
				result[i] = (new SafeSubstitution(m_Script, substitutionMapping)).transform(terms[i]);
			}
			return result;
		}
		
		/**
		 * Returns a String that we use to refer to the array cell array[index].
		 */
		private String getArrayCellName(TermVariable array, List<Term> index) {
			return "arrayCell_" + array.toString() + index.toString();
		}
		
		public void dotSomething() {
			for (int i=0; i<sunnf.length; i++) {
				for (TermVariable instance : m_ArrayGenealogy[i].getInstances()) {
					TermVariable originalGeneration = m_ArrayGenealogy[i].getProgenitor(instance);
					Map<List<Term>, TermVariable> index2ArrayCellTv = new HashMap<List<Term>, TermVariable>();
					for (List<Term> index : m_Array2Indices.getImage(originalGeneration)) {
						TermVariable tv = constructTermVariable(instance, index);
						index2ArrayCellTv.put(index, tv);
						boolean isInVarCell = isInVarCell(instance, index);
						boolean isOutVarCell = isOutVarCell(instance, index);
						if (isInVarCell || isOutVarCell) {
							TermVariable arrayRepresentative = (TermVariable) getDefinition(instance);
							ReplacementVar rv = getOrConstructReplacementVar(arrayRepresentative, index);
							if (isInVarCell) {
								m_VarCollector.addInVar(rv, tv);
							}
							if (isOutVarCell) {
								m_VarCollector.addOutVar(rv, tv);
							}
						} else {
							addToAuxVars(tv);
						}
					}
					m_ArrayInstance2Index2CellVariable.put(instance, index2ArrayCellTv);
				}
			}
		}
		

		private void addToAuxVars(TermVariable tv) {
			m_AuxVars.add(tv);
			//assert false : "not yet implemented";
		}

		private TermVariable constructTermVariable(TermVariable instance, List<Term> index) {
			Sort arraySort = instance.getSort();
			assert arraySort.isArraySort();
			MultiDimensionalArraySort mdias = new MultiDimensionalArraySort(arraySort);
			assert mdias.getDimension() == index.size();
			Sort valueSort = mdias.getArrayCellSort();
			String name = getArrayCellName(instance, index);
			TermVariable tv = m_VarCollector.getFactory().getNewTermVariable(name, valueSort);
			return tv;
		}

		private ReplacementVar constructReplacementVar(TermVariable array, List<Term> index) {
			String name = getArrayCellName(array, index);
			Term definition = SmtUtils.multiDimensionalSelect(m_Script, array, index.toArray(new Term[0]));
			return new ReplacementVar(name, definition); 
		}

		
		/**
		 * Is the cellVariable that we construct for arrayInstance[index] is
		 * an inVar. This is the case if arrayInstance and each free variable
		 * of index is an inVar.
		 */
		private boolean isInVarCell(TermVariable arrayInstance, List<Term> index) {
			if (isInvar(arrayInstance)) {
				for (Term indexEntry : index) {
					for (TermVariable tv : indexEntry.getFreeVars()) {
						if(!isInvar(tv)) {
							return false;
						}
					}
				}
				return true;
			} else {
				return false;
			}
		}
		
		private boolean isOutVarCell(TermVariable arrayInstance, List<Term> index) {
			if (isOutvar(arrayInstance)) {
				for (Term indexEntry : index) {
					for (TermVariable tv : indexEntry.getFreeVars()) {
						if(!isOutvar(tv)) {
							return false;
						}
					}
				}
				return true;
			} else {
				return false;
			}
		}
		
		
		private boolean isInvar(TermVariable tv) {
			return m_VarCollector.getInVarsReverseMapping().keySet().contains(tv);
		}
		
		private boolean isOutvar(TermVariable tv) {
			return m_VarCollector.getOutVarsReverseMapping().keySet().contains(tv);
		}

		public Map<TermVariable, Map<List<Term>, TermVariable>> getArrayInstance2Index2CellVariable() {
			return m_ArrayInstance2Index2CellVariable;
		}

		public Set<TermVariable> getAuxVars() {
			return m_AuxVars;
		}
		
		
		
	}
	
	private Term buildArrayUpdateConstraints(List<ArrayUpdate> arrayUpdates) {
		Term[] conjuncts = new Term[arrayUpdates.size()];
		int offset = 0;
		for (ArrayUpdate au : arrayUpdates) {
			conjuncts[offset] = buildArrayUpdateConstraints(au.getNewArray(), au.getOldArray(), au.getIndex(), au.getData());
			offset++;
		}
		return Util.and(m_Script, conjuncts);
	}
	
	
	private Term buildArrayUpdateConstraints(TermVariable newArray,
			TermVariable oldArray, Term[] updateIndex, Term data) {
		Map<List<Term>, TermVariable> newInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(newArray);
		Map<List<Term>, TermVariable> oldInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(oldArray);
		Term[] conjuncts = new Term[newInstance2Index2CellVariable.keySet().size()];
		int offset = 0;
		for (List<Term> index : newInstance2Index2CellVariable.keySet()) {
			Term newCellVariable = newInstance2Index2CellVariable.get(index);
			Term oldCellVariable = oldInstance2Index2CellVariable.get(index);
			Term indexIsUpdateIndex = SmtUtils.pairwiseEquality(m_Script, index.toArray(new Term[0]), updateIndex);
			Term newDataIsUpdateData = SmtUtils.binaryEquality(m_Script, newCellVariable, data);
			Term newDateIsOldData = SmtUtils.binaryEquality(m_Script, newCellVariable, oldCellVariable);
			Term indexIsNotUpdateIndex = Util.not(m_Script, indexIsUpdateIndex);
			Term indexIsUpdateIndexImpliesUpdateData = Util.or(m_Script, indexIsNotUpdateIndex, newDataIsUpdateData);
			Term indexIsNotUpdateIndexImpliesOldData = Util.or(m_Script, indexIsUpdateIndex, newDateIsOldData);
			conjuncts[offset] = Util.and(m_Script, indexIsUpdateIndexImpliesUpdateData, indexIsNotUpdateIndexImpliesOldData);
			offset++;
		}
		return Util.and(m_Script, conjuncts);
	}

	private Term buildIndexValueConstraints() {
		Term[] conjuncts = new Term[m_ArrayInstance2Index2CellVariable.size()];
		int offset = 0;
		for (Entry<TermVariable, Map<List<Term>, TermVariable>> entry : m_ArrayInstance2Index2CellVariable.entrySet()) {
			Map<List<Term>, TermVariable> indices2values = entry.getValue();
			conjuncts[offset] = buildIndexValueConstraints(indices2values);
			offset++;
		}
		return Util.and(m_Script, conjuncts);
	}

	private Term buildIndexValueConstraints(Map<List<Term>, TermVariable> indices2values) {
		List<Term>[] indices = new List[indices2values.size()];
		Term[] values = new Term[indices2values.size()];
		int offset = 0;
		for (Entry<List<Term>, TermVariable> index2value : indices2values.entrySet()) {
			indices[offset] = index2value.getKey();
			values[offset] = index2value.getValue();
			offset++;
		}
		int numberOfPairs = indices2values.size()*(indices2values.size()-1)/2;
		Term[] conjuncts = new Term[numberOfPairs];
		int k = 0;
		for (int i=0; i<indices2values.size(); i++) {
			for (int j=0; j<i; j++) {
				List<Term> index1 = indices[i];
				List<Term> index2 = indices[j];
				Term value1 = values[i];
				Term value2 = values[j];
				conjuncts[k] = indexEqualityImpliesValueEquality(index1.toArray(new Term[0]), index2.toArray(new Term[0]), value1, value2);
				k++;
			}
		}
		Term result = Util.and(m_Script, conjuncts);
		return result;
	}

	private Term indexEqualityImpliesValueEquality(Term[] index1,
			Term[] index2, Term value1, Term value2) {
		Term indexEquality = SmtUtils.pairwiseEquality(m_Script, index1, index2);
		Term valueEquality = SmtUtils.binaryEquality(m_Script, value1, value2);
		return Util.or(m_Script, Util.not(m_Script, indexEquality), valueEquality);
	}
	
	/**
	 * Replace all select terms by the corresponding cell variables.
	 * Replace all array updates by true. 
	 */
	private Term removeArrayUpdateAndArrayReads(Term term) {
		Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
		for (int i=0; i<sunnf.length; i++) {
			for (MultiDimensionalSelect ar : m_ArrayReads[i]) {
				Term cellVariable = m_ArrayInstance2Index2CellVariable.get(ar.getArray()).get(Arrays.asList(ar.getIndex()));
				substitutionMapping.put(ar.getSelectTerm(), cellVariable);
			}
			for (ArrayUpdate au : m_ArrayUpdates[i]) {
				substitutionMapping.put(au.getArrayUpdateTerm(), m_Script.term("true"));
			}
		}
		Term result = (new SafeSubstitution(m_Script, substitutionMapping)).transform(term);
		return result;
	}
	
	
	private static void isArrayFree(Term term) {
		for (TermVariable tv : term.getFreeVars()) {
			assert !tv.getSort().isArraySort();
		}
		Set<ApplicationTerm> selectTerms = 
				(new ApplicationTermFinder("select", true)).findMatchingSubterms(term);
		assert selectTerms.isEmpty();
		Set<ApplicationTerm> storeTerms = 
				(new ApplicationTermFinder("store", true)).findMatchingSubterms(term);
		assert storeTerms.isEmpty();
	}
	
	private class ArrayEquality {
		private final Term m_OriginalTerm;
		private TermVariable m_InVar;
		private TermVariable m_OutVar;
		
		public ArrayEquality(Term term) throws ArrayEqualityException {
			if (!(term instanceof ApplicationTerm)) {
				throw new ArrayEqualityException("no ApplicationTerm");
			}
			ApplicationTerm eqAppTerm = (ApplicationTerm) term;
			if (!eqAppTerm.getFunction().getName().equals("=")) {
				throw new ArrayEqualityException("no equality");
			}
			if (!(eqAppTerm.getParameters().length == 2)) {
				throw new ArrayEqualityException("no binary equality");
			}
			m_OriginalTerm = term;
			Term lhsTerm = eqAppTerm.getParameters()[0];
			Term rhsTerm = eqAppTerm.getParameters()[1];
			TermVariable lhs;
			if (lhsTerm instanceof TermVariable) {
				lhs = (TermVariable) lhsTerm;
			} else {
				throw new ArrayEqualityException("no tv");
			}
			TermVariable rhs;
			if (rhsTerm instanceof TermVariable) {
				rhs = (TermVariable) rhsTerm;
			} else {
				throw new ArrayEqualityException("no tv");
			}
			if (m_VarCollector.getInVarsReverseMapping().containsKey(lhs)) {
				m_InVar = lhs;
			} else if (m_VarCollector.getOutVarsReverseMapping().containsKey(lhs)) {
				m_OutVar = lhs;
			} else {
				throw new ArrayEqualityException("lhs neither in nor out");
			}
			if (m_VarCollector.getInVarsReverseMapping().containsKey(rhs)) {
				m_InVar = rhs;
			} else if (m_VarCollector.getOutVarsReverseMapping().containsKey(rhs)) {
				m_OutVar = rhs;
			} else {
				throw new ArrayEqualityException("rhs neither in nor out");
			}
		}
	}
	
	
	public static class ArrayEqualityException extends Exception {

		private static final long serialVersionUID = -5344050289008681972L;

		public ArrayEqualityException(String message) {
			super(message);
		}
	}
}