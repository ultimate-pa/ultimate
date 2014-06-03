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
import de.uni_freiburg.informatik.ultimate.logic.UtilExperimental;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.RankVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.VarCollector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.ElimStore3.ArrayRead;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.ElimStore3.ArrayReadException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.ElimStore3.ArrayStoreDef;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.ElimStore3.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.ElimStore3.ArrayUpdateException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.SmtUtils;
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
	
	
	Map<TermVariable, TermVariable> m_Instance2OriginalGeneration;
	private HashRelation<TermVariable, List<Term>> m_Array2Indices;
	List<ArrayUpdate> m_ArrayUpdates;
	List<ArrayRead> m_ArrayReads;
	Term m_Term;
	private Map<TermVariable, Map<List<Term>, TermVariable>> m_ArrayInstance2Index2CellVariable;
	
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
		assert m_Script == null;
		m_Script = script;
		SingleUpdateNormalFormTransformer sunnf = new SingleUpdateNormalFormTransformer(term);
		m_ArrayUpdates = sunnf.getArrayUpdates();
		m_Instance2OriginalGeneration = sunnf.getOriginalGeneration();
		m_Term = sunnf.getTerm();
		m_ArrayReads = extractArrayReads(m_Term);
		new IndexCollector();
		CellVariableBuilder cvb = new CellVariableBuilder();
		m_ArrayInstance2Index2CellVariable = cvb.getArrayInstance2Index2CellVariable();
		Term indexValueConstraints = buildIndexValueConstraints();
		Term arrayUpdateConstraints = buildArrayUpdateConstraints();
		Term removed = removeArrayUpdateAndArrayReads(m_Term);
		Term ivcRemoved = removeArrayUpdateAndArrayReads(indexValueConstraints);
		Term aucRemoved = removeArrayUpdateAndArrayReads(arrayUpdateConstraints);
		m_VarCollector.addAuxVars(cvb.getAuxVars());

		
//			assert !s_CheckResult || !isIncorrect(term, result, repTerm) 
//					: "rewrite division unsound";
//			assert !s_CheckResultWithQuantifiers
//					||	!isIncorrectWithQuantifiers(term, result, repTerm) 
//					: "rewrite division unsound";
		return Util.and(m_Script, ivcRemoved, aucRemoved, removed);
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
	

	
	private List<ArrayStoreDef> extractArrayStores(Term term) {
		List<ArrayStoreDef> asds = new ArrayList<ArrayStoreDef>();
		Set<ApplicationTerm> storeTerms = 
				(new ApplicationTermFinder("store", false)).findMatchingSubterms(term);
		for (Term storeTerm : storeTerms) {
			ArrayStoreDef asd;
			try {
				asd = new ArrayStoreDef(storeTerm);
			} catch (ArrayReadException e) {
				throw new UnsupportedOperationException("unexpected store term");
			}
			asds.add(asd);
		}
		return asds;
	}
	
	private class SingleUpdateNormalFormTransformer {
		Map<TermVariable, TermVariable> m_Instance2OriginalGeneration = new HashMap<TermVariable, TermVariable>();
		List<ArrayUpdate> m_ArrayUpdates;
		
		Term m_Term;
		/**
		 * If array a2 is defined as a2 = ("store", a1, index, value) we call
		 * a1 the parent generation of a2.  
		 */
		Map<TermVariable, TermVariable> m_ParentGeneration = new HashMap<TermVariable, TermVariable>();
		
		
		
		public SingleUpdateNormalFormTransformer(Term term) {
			super();
			m_Term = term;
			doTransform();
			for (ArrayUpdate au : m_ArrayUpdates) {
				m_ParentGeneration.put(au.getNewArray(), au.getOldArray());
			}
			for (TermVariable tv : m_ParentGeneration.keySet()) {
				TermVariable fg = getFirstGeneration(tv);
				m_Instance2OriginalGeneration.put(tv, fg);
				// we add first generation several times, probably
				// less expensive than checking if already inserted
				m_Instance2OriginalGeneration.put(fg, fg);

			}
		}
		
		public TermVariable getFirstGeneration(TermVariable tv) {
			TermVariable parent = m_ParentGeneration.get(tv);
			if (parent == null) {
				return tv;
			} else {
				return getFirstGeneration(parent);
			}
		}

		private void doTransform() {
			boolean m_EachArrayHasSingleUpdate = false;
			while(!m_EachArrayHasSingleUpdate) {
				Object result = eachArrayHasSingleUpdate();
				if (result instanceof ArrayStoreDef) {
					update((ArrayStoreDef) result);
				} else {
					m_EachArrayHasSingleUpdate = true;
					m_ArrayUpdates = (List<ArrayUpdate>) result;
				}
			}
		}
		
		private Object eachArrayHasSingleUpdate() {
			List<ArrayUpdate> arrayUpdates = new ArrayList<ArrayUpdate>();
			List<ArrayStoreDef> arrayStores = extractArrayStores(m_Term);
			for (ArrayStoreDef arrayStore : arrayStores) {
				ArrayUpdate au = findCorrespondingArrayUpdate(m_Term, arrayStore);
				arrayUpdates.add(au);
				if (au == null) {
					return arrayStore;
				}
			}
			assert (arrayStores.size() == arrayUpdates.size());
			return arrayUpdates;
		}
		
		private void update(ArrayStoreDef arraryStore) {
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

		private ArrayUpdate findCorrespondingArrayUpdate(Term term, ArrayStoreDef asd) {
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
						throw new AssertionError();
					}
				}
			}
			return null;
		}

		public List<ArrayUpdate> getArrayUpdates() {
			return Collections.unmodifiableList(m_ArrayUpdates);
		}

		public Map<TermVariable, TermVariable> getOriginalGeneration() {
			return Collections.unmodifiableMap(m_Instance2OriginalGeneration);
		}

		public Term getTerm() {
			return m_Term;
		}
	}
	

	private static List<ArrayRead> extractArrayReads(Term term) {
		Set<ApplicationTerm> selectTerms = 
				(new ApplicationTermFinder("select", true)).findMatchingSubterms(term);
		List<ArrayRead> arrayReads = new ArrayList<ArrayRead>();
		for (ApplicationTerm selectTerm : selectTerms) {
			try {
				ArrayRead ar = new ArrayRead(selectTerm);
				arrayReads.add(ar);
			} catch (ArrayReadException e) {
				// TODO Auto-generated catch block
				throw new AssertionError();
			}
		}
		return arrayReads;
	}
	
	
	private class IndexCollector {
		
		public IndexCollector() {
			super();
			m_Array2Indices = new HashRelation<TermVariable, List<Term>>();
			for(ArrayUpdate au : m_ArrayUpdates) {
				TermVariable firstGeneration = m_Instance2OriginalGeneration.get(au.getOldArray());
				Term[] index = au.getIndex();
				m_Array2Indices.addPair(firstGeneration, Arrays.asList(index));
			}
			for (ArrayRead ar : m_ArrayReads) {
				TermVariable firstGeneration = m_Instance2OriginalGeneration.get(ar.getArray());
				Term[] index = ar.getIndex();
				m_Array2Indices.addPair(firstGeneration, Arrays.asList(index));
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
			Map<List<Term>, ReplacementVar> index2repVar = m_Array2Index2RepVar.get(array);
			if (index2repVar == null) {
				index2repVar = new HashMap<List<Term>, ReplacementVar>();
				m_Array2Index2RepVar.put(array, index2repVar);
			}
			ReplacementVar repVar = index2repVar.get(index);
			if (repVar == null) {
				repVar = constructReplacementVar(array, index);
				index2repVar.put(index, repVar);
			}
			return repVar;
		}
		
		/**
		 * Returns a String that we use to refer to the array cell array[index].
		 */
		private String getArrayCellName(TermVariable array, List<Term> index) {
			return "arrayCell_" + array.toString() + index.toString();
		}
		
		public void dotSomething() {
			for (TermVariable instance : m_Instance2OriginalGeneration.keySet()) {
				TermVariable originalGeneration = m_Instance2OriginalGeneration.get(instance);
				Map<List<Term>, TermVariable> index2ArrayCellTv = new HashMap<List<Term>, TermVariable>();
				for (List<Term> index : m_Array2Indices.getImage(originalGeneration)) {
					TermVariable tv = constructTermVariable(instance, index);
					index2ArrayCellTv.put(index, tv);
					boolean isInVarCell = isInVarCell(instance, index);
					boolean isOutVarCell = isOutVarCell(instance, index);
					if (isInVarCell || isOutVarCell) {
						TermVariable arrayRepresentative = getRepresentative(instance);
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
		
		private TermVariable getRepresentative(TermVariable instance) {
			RankVar rv = m_VarCollector.getInVarsReverseMapping().get(instance);
			if (rv == null) {
				rv = m_VarCollector.getOutVarsReverseMapping().get(instance);
			}
			if (rv == null) {
				throw new AssertionError();
			}
			Term definition = rv.getDefinition();
			if (definition instanceof TermVariable) {
				return (TermVariable) definition;
			} else {
				throw new AssertionError();
			}
		}
		
		private void addToAuxVars(TermVariable tv) {
			m_AuxVars.add(tv);
			//assert false : "not yet implemented";
		}

		private TermVariable constructTermVariable(TermVariable instance, List<Term> index) {
			Sort arraySort = instance.getSort();
			assert arraySort.isArraySort();
			assert arraySort.getArguments().length == index.size()+1;
			Sort valueSort = arraySort.getArguments()[arraySort.getArguments().length-1];
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
	
	private Term buildArrayUpdateConstraints() {
		Term[] conjuncts = new Term[m_ArrayUpdates.size()];
		int offset = 0;
		for (ArrayUpdate au : m_ArrayUpdates) {
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
			Term newDataIsUpdateData = UtilExperimental.binaryEquality(m_Script, newCellVariable, data);
			Term newDateIsOldData = UtilExperimental.binaryEquality(m_Script, newCellVariable, oldCellVariable);
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
		Term valueEquality = UtilExperimental.binaryEquality(m_Script, value1, value2);
		return Util.or(m_Script, Util.not(m_Script, indexEquality), valueEquality);
	}
	
	/**
	 * Replace all select terms by the corresponding cell variables.
	 * Replace all array updates by true. 
	 */
	private Term removeArrayUpdateAndArrayReads(Term term) {
		Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
		for (ArrayRead ar : m_ArrayReads) {
			Term cellVariable = m_ArrayInstance2Index2CellVariable.get(ar.getArray()).get(Arrays.asList(ar.getIndex()));
			substitutionMapping.put(ar.getSelectTerm(), cellVariable);
		}
		for (ArrayUpdate au : m_ArrayUpdates) {
			substitutionMapping.put(au.getArrayUpdateTerm(), m_Script.term("true"));
		}
		Term result = (new SafeSubstitution(m_Script, substitutionMapping)).transform(term);
		return result;
	}
	
}