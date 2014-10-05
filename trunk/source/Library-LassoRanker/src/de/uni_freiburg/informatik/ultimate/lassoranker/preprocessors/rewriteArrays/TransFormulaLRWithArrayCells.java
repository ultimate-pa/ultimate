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
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.relation.Triple;

/**
 * Computes and provides for a TransformulaLR a DNF of the formula and 
 * information 
 * - which arrays occur in the formula,
 * - in which order the arrays are written,
 * - and the possible indices of each Array accesses.
 * 
 * @author Matthias Heizmann
 */
public class TransFormulaLRWithArrayCells {

	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;
	
	static final String s_AuxArray = "auxArray";

	/**
	 * The script used to transform the formula
	 */
	private final Script m_Script;
	


	
	private final NestedMap2<TermVariable, ArrayIndex, ArrayCellReplacementVarInformation> m_ForeignReplacementVars =
			new NestedMap2<TermVariable, ArrayIndex, ArrayCellReplacementVarInformation>();
	private final HashRelation<TermVariable, ArrayIndex> m_ForeignIndices = new HashRelation<>();
	
	private final TransFormulaLRWithArrayInformation tflrwai;
	private final TransFormulaLR m_Result;
	private final ReplacementVarFactory m_ReplacementVarFactory;
	private Map<TermVariable, Map<ArrayIndex, TermVariable>> m_ArrayInstance2Index2CellVariable;
	private EquivalentCells[] m_EquivalentCells;
	private boolean m_OverapproximateByOmmitingDisjointIndices;
	private HashRelation<TermVariable, ArrayIndex> m_FirstGeneration2Indices;
	private IndexAnalyzer2 indexAnalyzer;
	private NestedMap2<TermVariable, ArrayIndex, ArrayCellReplacementVarInformation> m_ArrayCellInVars;
	private NestedMap2<TermVariable, ArrayIndex, ArrayCellReplacementVarInformation> m_ArrayCellOutVars;
	
	private final Map<List<Term>, ArrayIndex> m_IndexInstance2IndexRepresentative = new HashMap<>();

	public TransFormulaLRWithArrayCells(
			IUltimateServiceProvider services, 
			ReplacementVarFactory replacementVarFactory, Script script,
			TransFormulaLRWithArrayInformation tflrwai, 
			IndexSupportingInvariantAnalysis indexSupportingInvariantAnalysis, 
			Boogie2SMT boogie2smt, ArrayCellRepVarConstructor acrvc) {
			mServices = services;
			mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
			this.tflrwai = tflrwai;
			m_Script = script;
			m_ReplacementVarFactory = replacementVarFactory;
			if (!this.tflrwai.containsArrays()) {
				m_Result = this.tflrwai.getTransFormulaLR();
				return;
			}
			m_Result = new TransFormulaLR(tflrwai.getTransFormulaLR());
			m_FirstGeneration2Indices = new HashRelation<>();
			m_FirstGeneration2Indices.addAll(tflrwai.getArrayFirstGeneration2Indices());
			if (acrvc != null) {
				addForeignReplacementVars(acrvc);
			}
			m_ArrayCellInVars = new NestedMap2<>();
			m_ArrayCellInVars.addAll(tflrwai.getArrayCellInVars());
			m_ArrayCellInVars.addAll(m_ForeignReplacementVars);
			m_ArrayCellOutVars = new NestedMap2<>();
			m_ArrayCellOutVars.addAll(tflrwai.getArrayCellOutVars());
			m_ArrayCellOutVars.addAll(m_ForeignReplacementVars);

			doSomething();
			
			
			
			indexAnalyzer = new IndexAnalyzer2(m_Result.getFormula(), m_FirstGeneration2Indices, boogie2smt, m_Result, indexSupportingInvariantAnalysis);
			CellVariableBuilder cvb = new CellVariableBuilder(m_Result, this, replacementVarFactory, mLogger, m_FirstGeneration2Indices, m_ArrayCellInVars, m_ArrayCellOutVars);
			m_ArrayInstance2Index2CellVariable = cvb.getArrayInstance2Index2CellVariable();
			m_EquivalentCells = new EquivalentCells[tflrwai.numberOfDisjuncts()];
			for (int i = 0; i < tflrwai.numberOfDisjuncts(); i++) {
				m_EquivalentCells[i] = new EquivalentCells(m_Script, m_Result, tflrwai.getArrayEqualities().get(i), tflrwai.getArrayUpdates().get(i), indexAnalyzer, m_ArrayInstance2Index2CellVariable); 
//						computeEquivalentCells(m_Result, tflrwai.getArrayEqualities().get(i), tflrwai.getArrayUpdates().get(i));
			}

			SafeSubstitution[] m_Select2CellVariable = new SafeSubstitution[tflrwai.numberOfDisjuncts()];
			for (int i = 0; i < tflrwai.numberOfDisjuncts(); i++) {
				m_Select2CellVariable[i] = constructIndex2CellVariableSubstitution(m_EquivalentCells[i], i);
			}

			Term[] arrayEqualityConstraints = new Term[tflrwai.numberOfDisjuncts()];
			for (int i = 0; i < tflrwai.numberOfDisjuncts(); i++) {
				arrayEqualityConstraints[i] = m_EquivalentCells[i].getInOutEqauality();
			}

			Term[] indexValueConstraints = new Term[tflrwai.numberOfDisjuncts()];
			for (int i = 0; i < tflrwai.numberOfDisjuncts(); i++) {
				indexValueConstraints[i] = buildIndexValueConstraints(m_Select2CellVariable[i], m_EquivalentCells[i]);
			}

			Term[] arrayUpdateConstraints = new Term[tflrwai.numberOfDisjuncts()];
			for (int i = 0; i < tflrwai.numberOfDisjuncts(); i++) {
				arrayUpdateConstraints[i] = buildArrayUpdateConstraints(tflrwai.getArrayUpdates().get(i), m_Select2CellVariable[i],
						m_EquivalentCells[i]);
			}
			Term[] disjunctsWithUpdateConstraints = new Term[tflrwai.numberOfDisjuncts()];
			for (int i = 0; i < disjunctsWithUpdateConstraints.length; i++) {
				Term removedSelect = m_Select2CellVariable[i].transform(tflrwai.getSunnf()[i]);
				Term[] conjuncts;
				if (m_OverapproximateByOmmitingDisjointIndices) {
					conjuncts = new Term[5];
				} else {
					conjuncts = new Term[6];
					conjuncts[5] = indexAnalyzer.getAdditionalConjunctsNotEquals();
				}
				conjuncts[0] = removedSelect;
				conjuncts[1] = indexValueConstraints[i];
				conjuncts[2] = arrayUpdateConstraints[i];
				conjuncts[3] = arrayEqualityConstraints[i];
				conjuncts[4] = indexAnalyzer.getAdditionalConjunctsEqualities();
				disjunctsWithUpdateConstraints[i] = Util.and(m_Script, conjuncts);
			}
			Term resultDisjuntion = Util.or(m_Script, disjunctsWithUpdateConstraints);
			HashSet<TermVariable> auxVars = new HashSet<TermVariable>(cvb.getAuxVars());

			Term result = //resultDisjuntion;
					PartialQuantifierElimination.elim(m_Script, QuantifiedFormula.EXISTS, auxVars, resultDisjuntion, mServices, mLogger);
			
			assert SmtUtils.isArrayFree(result) : "Result contains still arrays!";
			result = SmtUtils.simplify(m_Script, result, mLogger);
			
			removeArrayInOutVars();
			
			m_Result.setFormula(result);
			m_Result.addAuxVars(auxVars);
	}
	
	private void removeArrayInOutVars() {
		{
			List<RankVar> toRemove = new ArrayList<RankVar>();
			toRemove.addAll(filterArrays(m_Result.getInVars().keySet()));
			for (RankVar rv : toRemove) {
				m_Result.removeInVar(rv);
			}
		}
		{
			List<RankVar> toRemove = new ArrayList<RankVar>();
			toRemove.addAll(filterArrays(m_Result.getOutVars().keySet()));
			for (RankVar rv : toRemove) {
				m_Result.removeOutVar(rv);
			}
		}
	}

	private Collection<RankVar> filterArrays(Set<RankVar> keySet) {
		List<RankVar> result = new ArrayList<RankVar>();
		for (RankVar rv : keySet) {
			if (rv.getDefinition().getSort().isArraySort()) {
				result.add(rv);
			}
		}
		return result;
	}

	public ArrayIndex getOrConstructIndexRepresentative(ArrayIndex indexInstance) {
		ArrayIndex indexRepresentative = m_IndexInstance2IndexRepresentative.get(indexInstance);
		if (indexRepresentative == null) {
			indexRepresentative = new ArrayIndex(TransFormulaUtils.translateTermVariablesToDefinitions(m_Script, m_Result, indexInstance));
			m_IndexInstance2IndexRepresentative.put(indexInstance, indexRepresentative);
		}
		return indexRepresentative;
	}
	
	
	
	public TransFormulaLRWithArrayInformation getTransFormulaLRWithArrayInformation() {
		return tflrwai;
	}



	private void addForeignReplacementVars(ArrayCellRepVarConstructor arrayCellRepVarConstructor) {
		NestedMap2<TermVariable, ArrayIndex, ArrayCellReplacementVarInformation> array2Index2RepVar = 
				arrayCellRepVarConstructor.getArrayRepresentative2IndexRepresentative2ReplacementVar();
		for (TermVariable array : array2Index2RepVar.keySet()) {
			if (arrayOccursInThisTransFormulaAsInvar(array)) {
				for (Entry<ArrayIndex, ArrayCellReplacementVarInformation> entry : array2Index2RepVar.get(array).entrySet()) {
					ArrayIndex index = entry.getKey();
					ArrayCellReplacementVarInformation acrvi = entry.getValue();
					if (allVarsOfIndexOccurInThisTransFormulaAsInvar(acrvi)) {
						if (!arrayCellOccursInThisTransFormula(array, index)) {
							m_ForeignReplacementVars.put(array, index, entry.getValue());
						}
					}
				}
			}
		}
	}
	
	private boolean allVarsOfIndexOccurInThisTransFormulaAsInvar(
			ArrayCellReplacementVarInformation acrvi) {
		Collection<RankVar> rankVarsOccurringInIndex = acrvi.termVariableToRankVarMappingForIndex().values();
		for (RankVar rv : rankVarsOccurringInIndex) {
			if (!this.tflrwai.getTransFormulaLR().getInVars().containsKey(rv)) {
				return false;
			}
		}
		return true;
	}

	public void doSomething() {
		for (Triple<TermVariable, ArrayIndex, ArrayCellReplacementVarInformation> triple  : m_ForeignReplacementVars.entrySet()) {
			ArrayCellReplacementVarInformation acrvi = triple.getThird();
			assert acrvi.getArrayRepresentative().equals(triple.getFirst());
			assert acrvi.getIndexRepresentative().equals(triple.getSecond());
			Collection<RankVar> rankVarsOccurringInIndex = acrvi.termVariableToRankVarMappingForIndex().values();
			for (RankVar rv : rankVarsOccurringInIndex) {
				if (!rankVarOccursInThisTransformula(rv, m_Result)) {
					addRankVar(rv);
					throw new AssertionError("case may not occur any more");
				}
			}
			TermVariable translatedArray = (TermVariable) tflrwai.getTransFormulaLR().getInVars().get(acrvi.getArrayRankVar());
			ArrayIndex translatedIndex = translateIndex(acrvi.getIndex(), acrvi.termVariableToRankVarMappingForIndex());
			m_FirstGeneration2Indices.addPair(translatedArray, translatedIndex);
		}
	}
	
	
	
	private ArrayIndex translateIndex(ArrayIndex index,
			Map<TermVariable, RankVar> termVariableToRankVarMappingForIndex) {
		List<Term> translatedIndex = new ArrayList<Term>();
		for (Term entry : index) {
			Term translatedEntry = translateIndexEntry(entry, termVariableToRankVarMappingForIndex);
			translatedIndex.add(translatedEntry);
		}
		return new ArrayIndex(translatedIndex);
	}

	private Term translateIndexEntry(Term entry,
			Map<TermVariable, RankVar> termVariableToRankVarMappingForIndex) {
		Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
		for (TermVariable originalTv : entry.getFreeVars()) {
			RankVar rv = termVariableToRankVarMappingForIndex.get(originalTv);
			TermVariable newTv = (TermVariable) m_Result.getInVars().get(rv);
			substitutionMapping.put(originalTv, newTv);
		}
		Term renamedEntry = (new SafeSubstitution(m_Script, substitutionMapping)).transform(entry);
		return renamedEntry;
	}

	private void addRankVar(RankVar rv) {
		String name = SmtUtils.removeSmtQuoteCharacters(rv.getGloballyUniqueId() + "_InOut");
		Sort sort = rv.getDefinition().getSort();
		TermVariable tv = m_ReplacementVarFactory.getOrConstructAuxVar(name, sort);
		m_Result.addInVar(rv, tv);
		m_Result.addOutVar(rv, tv);
	}

	private boolean rankVarOccursInThisTransformula(RankVar rv,
			TransFormulaLR transFormulaLR) {
		Term inVar = transFormulaLR.getInVars().get(rv);
		Term outVar = transFormulaLR.getOutVars().get(rv);
		if (inVar == null && outVar == null) {
			return false;
		}
		if (inVar != null && outVar != null) {
			return true;
		}
		throw new AssertionError(rv + " occurs only as inVar or only as outVar");
	}

	private boolean arrayOccursInThisTransFormulaAsInvar(TermVariable array) {
		return this.tflrwai.getArrayCellInVars().keySet().contains(array);
	}
	
	private boolean arrayCellOccursInThisTransFormula(TermVariable array, List<Term> index) {
		return this.tflrwai.getArrayCellInVars().get(array).containsKey(index);
//		||	this.tflrwai.getArrayCellOutVars().get(array).containsKey(index);
	}

	
	






	

	private Term buildArrayEqualityConstraints(TermVariable oldArray, TermVariable newArray) {
		Map<ArrayIndex, TermVariable> newInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(newArray);
		Map<ArrayIndex, TermVariable> oldInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(oldArray);
		if (newInstance2Index2CellVariable == null && oldInstance2Index2CellVariable == null) {
			return m_Script.term("true");
		}
		Term[] conjuncts = new Term[newInstance2Index2CellVariable.keySet().size()];
		int offset = 0;
		for (List<Term> index : newInstance2Index2CellVariable.keySet()) {
			Term newCellVariable = newInstance2Index2CellVariable.get(index);
			Term oldCellVariable = oldInstance2Index2CellVariable.get(index);
			conjuncts[offset] = SmtUtils.binaryEquality(m_Script, oldCellVariable, newCellVariable);
			offset++;
		}
		return Util.and(m_Script, conjuncts);
	}

	private Term buildArrayUpdateConstraints(List<ArrayUpdate> arrayUpdates, SafeSubstitution select2CellVariable,
			EquivalentCells equivalentCells) {
		Term[] conjuncts = new Term[arrayUpdates.size()];
		int offset = 0;
		for (ArrayUpdate au : arrayUpdates) {
			conjuncts[offset] = buildArrayUpdateConstraints(au.getNewArray(), au.getOldArray(), au.getIndex(),
					au.getValue(), select2CellVariable, equivalentCells);
			offset++;
		}
		Term result = Util.and(m_Script, conjuncts);
		assert (new ApplicationTermFinder("select", false)).findMatchingSubterms(result).isEmpty() : "contains select terms";
		return result;
	}

	private Term buildArrayUpdateConstraints(TermVariable newArray, TermVariable oldArray, ArrayIndex updateIndex,
			Term data, SafeSubstitution select2CellVariable, EquivalentCells equivalentCells) {
		data = select2CellVariable.transform(data);
		Map<ArrayIndex, TermVariable> newInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(newArray);
		Map<ArrayIndex, TermVariable> oldInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(oldArray);
		Term[] conjuncts = new Term[newInstance2Index2CellVariable.keySet().size()];
		int offset = 0;
		for (ArrayIndex index : newInstance2Index2CellVariable.keySet()) {
			TermVariable newCellVariable = newInstance2Index2CellVariable.get(index);
			newCellVariable = equivalentCells.getInOutRepresentative(newCellVariable);
			TermVariable oldCellVariable = oldInstance2Index2CellVariable.get(index);
			oldCellVariable = equivalentCells.getInOutRepresentative(oldCellVariable);
			Term indexIsUpdateIndex = pairwiseEqualityExploitDoubletons(index, updateIndex,
					select2CellVariable);
			Term newDataIsUpdateData = SmtUtils.binaryEquality(m_Script, newCellVariable, data);
			Term newDateIsOldData = SmtUtils.binaryEquality(m_Script, newCellVariable, oldCellVariable);
			Term indexIsNotUpdateIndex = Util.not(m_Script, indexIsUpdateIndex);
			Term indexIsUpdateIndexImpliesUpdateData = Util.or(m_Script, indexIsNotUpdateIndex, newDataIsUpdateData);
			Term indexIsNotUpdateIndexImpliesOldData = Util.or(m_Script, indexIsUpdateIndex, newDateIsOldData);
			conjuncts[offset] = Util.and(m_Script, indexIsUpdateIndexImpliesUpdateData,
					indexIsNotUpdateIndexImpliesOldData);
			offset++;
		}
		return Util.and(m_Script, conjuncts);
	}

	private Term buildIndexValueConstraints(SafeSubstitution select2CellVariable, EquivalentCells equivalentCells) {
		Term[] conjuncts = new Term[m_ArrayInstance2Index2CellVariable.size()];
		int offset = 0;
		for (Entry<TermVariable, Map<ArrayIndex, TermVariable>> entry : m_ArrayInstance2Index2CellVariable.entrySet()) {
			Map<ArrayIndex, TermVariable> indices2values = entry.getValue();
			conjuncts[offset] = buildIndexValueConstraints(indices2values, select2CellVariable, equivalentCells);
			offset++;
		}
		return Util.and(m_Script, conjuncts);
	}

	private Term buildIndexValueConstraints(Map<ArrayIndex, TermVariable> indices2values,
			SafeSubstitution select2CellVariable, EquivalentCells equivalentCells) {
		ArrayIndex[] indices = new ArrayIndex[indices2values.size()];
		TermVariable[] values = new TermVariable[indices2values.size()];
		int offset = 0;
		for (Entry<ArrayIndex, TermVariable> index2value : indices2values.entrySet()) {
			indices[offset] = index2value.getKey();
			values[offset] = index2value.getValue();
			offset++;
		}
		int numberOfPairs = indices2values.size() * (indices2values.size() - 1) / 2;
		Term[] conjuncts = new Term[numberOfPairs];
		int k = 0;
		for (int i = 0; i < indices2values.size(); i++) {
			for (int j = 0; j < i; j++) {
				ArrayIndex index1 = indices[i];
				ArrayIndex index2 = indices[j];
				TermVariable value1 = values[i];
				TermVariable value2 = values[j];
				TermVariable value1Representative = equivalentCells.getInOutRepresentative(value1);
				TermVariable value2Representative = equivalentCells.getInOutRepresentative(value2);
				conjuncts[k] = indexEqualityImpliesValueEquality(index1, index2, value1Representative,
						value2Representative, select2CellVariable);
				k++;
			}
		}
		Term result = Util.and(m_Script, conjuncts);
		return result;
	}

	private Term indexEqualityImpliesValueEquality(ArrayIndex index1, ArrayIndex index2, Term value1, Term value2,
			SafeSubstitution select2CellVariable) {
		Term indexEquality = pairwiseEqualityExploitDoubletons(index1, index2, select2CellVariable);
		Term valueEquality = SmtUtils.binaryEquality(m_Script, value1, value2);
		return Util.or(m_Script, Util.not(m_Script, indexEquality), valueEquality);
	}

	Term pairwiseEqualityExploitDoubletons(ArrayIndex index1, ArrayIndex index2, SafeSubstitution select2CellVariable) {
		assert index1.size() == index2.size();
		Term[] conjuncts = new Term[index1.size()];
		for (int i = 0; i < index1.size(); i++) {
			Term fst = index1.get(i);
			Term snd = index2.get(i);
			if (fst == snd || indexAnalyzer.isEqualDoubleton(fst, snd)) {
				conjuncts[i] = m_Script.term("true");
			} else if (indexAnalyzer.isDistinctDoubleton(fst, snd)) {
				conjuncts[i] = m_Script.term("false");
			} else if (indexAnalyzer.isUnknownDoubleton(fst, snd)) {
				Term fstSubst = select2CellVariable.transform(fst);
				Term sndSubst = select2CellVariable.transform(snd);
				conjuncts[i] = SmtUtils.binaryEquality(m_Script, fstSubst, sndSubst);
			} else {
				throw new AssertionError("unknown doubleton");
			}
		}
		return Util.and(m_Script, conjuncts);
	}

	/**
	 * Replace all select terms by the corresponding cell variables.
	 */
	private SafeSubstitution constructIndex2CellVariableSubstitution(EquivalentCells ec, int i) {
		Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
		for (MultiDimensionalSelect ar : tflrwai.getArrayReads().get(i)) {
			TermVariable cellVariable = m_ArrayInstance2Index2CellVariable.get(ar.getArray()).get(ar.getIndex());
			Term inOutRepresentative = ec.getInOutRepresentative(cellVariable);
			assert inOutRepresentative != null;
			substitutionMapping.put(ar.getSelectTerm(), inOutRepresentative);
		}

		for (MultiDimensionalSelect ar : tflrwai.getAdditionalArrayReads()) {
			TermVariable cellVariable = m_ArrayInstance2Index2CellVariable.get(ar.getArray()).get(ar.getIndex());
			Term inOutRepresentative = ec.getInOutRepresentative(cellVariable);
			assert inOutRepresentative != null;
			substitutionMapping.put(ar.getSelectTerm(), inOutRepresentative);
		}
		return new SafeSubstitution(m_Script, substitutionMapping);
	}



	public TransFormulaLR getResult() {
		return m_Result;
	}




}