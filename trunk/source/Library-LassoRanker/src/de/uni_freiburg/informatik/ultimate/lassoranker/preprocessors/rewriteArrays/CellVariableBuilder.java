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

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;

public class CellVariableBuilder {
	private final Map<TermVariable, Map<List<Term>, TermVariable>> m_ArrayInstance2Index2CellVariable;
	private final Map<TermVariable, Map<List<Term>, ReplacementVar>> m_Array2Index2RepVar;
	private final Set<TermVariable> m_AuxVars = new HashSet<TermVariable>();
	private final TransFormulaLR m_TransFormula;
	private final TransFormulaLRWithArrayInformation tflrwai;
	private final TransFormulaLRWithArrayCells tflrwac;
	private final ReplacementVarFactory m_ReplacementVarFactory;
	private final Logger mLogger;

	public CellVariableBuilder(TransFormulaLR tf, TransFormulaLRWithArrayCells tflrwac, ReplacementVarFactory replacementVarFactory, Logger logger) {
		m_ReplacementVarFactory = replacementVarFactory;
		mLogger = logger;
		m_TransFormula = tf;
		this.tflrwac = tflrwac;
		this.tflrwai = tflrwac.getTransFormulaLRWithArrayInformation();
		m_ArrayInstance2Index2CellVariable = new HashMap<TermVariable, Map<List<Term>, TermVariable>>();
		m_Array2Index2RepVar = new HashMap<TermVariable, Map<List<Term>, ReplacementVar>>();
		dotSomething();
	}


	/**
	 * Returns a String that we use to refer to the array cell array[index].
	 */
	private String getArrayCellName(TermVariable array, List<Term> index) {
		return "arrayCell_" + SmtUtils.removeSmtQuoteCharacters(array.toString())
				+ SmtUtils.removeSmtQuoteCharacters(index.toString());
	}

	public void dotSomething() {
		for (TermVariable firstGeneration : tflrwai.getArrayFirstGeneration2Instances().getDomain()) {
			for (TermVariable instance : tflrwai.getArrayFirstGeneration2Instances().getImage(firstGeneration)) {
				Map<List<Term>, TermVariable> index2ArrayCellTv = m_ArrayInstance2Index2CellVariable.get(instance);
				if (index2ArrayCellTv == null) {
					index2ArrayCellTv = new HashMap<List<Term>, TermVariable>();
					m_ArrayInstance2Index2CellVariable.put(instance, index2ArrayCellTv);
				}
				Set<List<Term>> indicesOfOriginalGeneration = tflrwai.getArrayFirstGeneration2Indices().getImage(firstGeneration);
				if (indicesOfOriginalGeneration == null) {
					mLogger.info("Array " + firstGeneration + " is never accessed");
					continue;
				}
				for (List<Term> index : indicesOfOriginalGeneration) {
					TermVariable tv = index2ArrayCellTv.get(index);
					if (tv == null) {
						tv = constructTermVariable(instance, index);
						index2ArrayCellTv.put(index, tv);
					}
					boolean isInVarCell = isInVarCell(instance, index);
					boolean isOutVarCell = isOutVarCell(instance, index);
					if (isInVarCell || isOutVarCell) {
						TermVariable arrayRepresentative = (TermVariable) tflrwai.getDefinition(firstGeneration);
						List<Term> indexRepresentative = tflrwai.getOrConstructIndexRepresentative(index);
						if (isInVarCell) {
							ReplacementVar rv = tflrwac.getTransFormulaLRWithArrayInformation().getArrayCellInVars().get(arrayRepresentative, indexRepresentative).getReplacementVar();
							if (!m_TransFormula.getInVars().containsKey(rv)) {
								m_TransFormula.addInVar(rv, tv);
							} else {
								assert m_TransFormula.getInVars().get(rv) == tv;
							}
						}
						if (isOutVarCell) {
							ReplacementVar rv = tflrwac.getTransFormulaLRWithArrayInformation().getArrayCellOutVars().get(arrayRepresentative, indexRepresentative).getReplacementVar();
							if (!m_TransFormula.getOutVars().containsKey(rv)) {
								m_TransFormula.addOutVar(rv, tv);
							} else {
								assert m_TransFormula.getOutVars().get(rv) == tv;
							}
						}
					} else {
						addToAuxVars(tv);
					}
				}

			}
		}
	}

	private void addToAuxVars(TermVariable tv) {
		m_AuxVars.add(tv);
		// assert false : "not yet implemented";
	}

	private TermVariable constructTermVariable(TermVariable instance, List<Term> index) {
		Sort arraySort = instance.getSort();
		assert arraySort.isArraySort();
		MultiDimensionalSort mdias = new MultiDimensionalSort(arraySort);
		assert mdias.getDimension() == index.size();
		Sort valueSort = mdias.getArrayValueSort();
		String name = getArrayCellName(instance, index);
		TermVariable tv = m_ReplacementVarFactory.
				getOrConstructAuxVar(name, valueSort);
		return tv;
	}

	/**
	 * Is the cellVariable that we construct for arrayInstance[index] is an
	 * inVar. This is the case if arrayInstance and each free variable of
	 * index is an inVar.
	 */
	private boolean isInVarCell(TermVariable arrayInstance, List<Term> index) {
		if (TransFormulaUtils.isInvar(arrayInstance, m_TransFormula)) {
			return TransFormulaUtils.allVariablesAreInVars(index, m_TransFormula);
		} else {
			return false;
		}
	}

	private boolean isOutVarCell(TermVariable arrayInstance, List<Term> index) {
		if (TransFormulaUtils.isOutvar(arrayInstance, m_TransFormula)) {
			return TransFormulaUtils.allVariablesAreOutVars(index, m_TransFormula);
		} else {
			return false;
		}
	}

	public Map<TermVariable, Map<List<Term>, TermVariable>> getArrayInstance2Index2CellVariable() {
		return m_ArrayInstance2Index2CellVariable;
	}

	public Set<TermVariable> getAuxVars() {
		return m_AuxVars;
	}

}
