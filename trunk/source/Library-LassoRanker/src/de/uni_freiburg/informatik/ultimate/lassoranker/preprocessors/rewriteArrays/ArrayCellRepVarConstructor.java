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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.relation.Triple;

/**
 * Construct all array cell ReplacementVar for a lasso.
 * If the array cell a[i] occurs in the lasso this class constructs a 
 * ReplacementVar for a[i].
 * Construct also a map that maps the pair (a,i) to one 
 * ArrayCellReplacementVarInformation.
 * (There may be several ArrayCellReplacementVarInformation for the same
 * ReplacementVar. We store one in order to have a possibility obtain all 
 * RankVars that occur in the index).
 * @author Matthias Heizmann
 *
 */
public class ArrayCellRepVarConstructor {
	
	private final ReplacementVarFactory m_ReplacementVarFactory;
	private final Script m_Script;
	private final NestedMap2<TermVariable, ArrayIndex, ArrayCellReplacementVarInformation> m_ArrayRepresentative2IndexRepresentative2ReplacementVar = new NestedMap2<>();
	private final List<TransFormulaLRWithArrayInformation> m_Stem;
	private final List<TransFormulaLRWithArrayInformation> m_Loop;
	
	public ArrayCellRepVarConstructor(
			ReplacementVarFactory replacementVarFactory, Script script,
			List<TransFormulaLRWithArrayInformation> stem,
			List<TransFormulaLRWithArrayInformation> loop) {
		super();
		m_ReplacementVarFactory = replacementVarFactory;
		m_Script = script;
		m_Stem = stem;
		m_Loop = loop;
		for (TransFormulaLRWithArrayInformation tfwac : m_Stem) {
			constructRepVars(tfwac);
		}
		for (TransFormulaLRWithArrayInformation tfwac : m_Loop) {
			constructRepVars(tfwac);
		}
	}


	private void constructRepVars(TransFormulaLRWithArrayInformation tfwac) {
		for (Triple<TermVariable, ArrayIndex, ArrayCellReplacementVarInformation> triple : tfwac.getArrayCellInVars().entrySet()) {
			ArrayCellReplacementVarInformation acrvi = triple.getThird();
			constructRepVarIfNecessaryAndAdd(acrvi);
		}
		for (Triple<TermVariable, ArrayIndex, ArrayCellReplacementVarInformation> triple : tfwac.getArrayCellOutVars().entrySet()) {
			ArrayCellReplacementVarInformation acrvi = triple.getThird();
			constructRepVarIfNecessaryAndAdd(acrvi);
		}
	}


	private void constructRepVarIfNecessaryAndAdd(
			ArrayCellReplacementVarInformation acrvi) {
		ReplacementVar repVar = getOrconstructReplacementVar(acrvi);
		acrvi.setReplacementVar(repVar);
	}
	
	/**
	 * Check if we already have a repVar for the same array/index as acrvi.
	 * If yes, return this repVar. If not construct a new one and add the acrvi
	 * to the map. We expect that the repVar is added to the acrvi by the 
	 * caller of this method.
	 */
	private ReplacementVar getOrconstructReplacementVar(ArrayCellReplacementVarInformation acrvi) {
		TermVariable array = acrvi.getArrayRepresentative();
		ArrayIndex index = acrvi.getIndexRepresentative();
		ArrayCellReplacementVarInformation repVarInfo = m_ArrayRepresentative2IndexRepresentative2ReplacementVar.get(array, index);
		ReplacementVar repVar;
		if (repVarInfo == null) {
			repVar = constructReplacementVar(array, index);
			m_ArrayRepresentative2IndexRepresentative2ReplacementVar.put(array, index, acrvi);
		} else {
			repVar = repVarInfo.getReplacementVar();
		}
		return repVar;
	}
	
	
	/**
	 * Returns a ReplacementVar that will represent the array
	 * cell array[index].
	 */
	private ReplacementVar constructReplacementVar(TermVariable array, ArrayIndex index) {
			Term definition = SmtUtils.multiDimensionalSelect(m_Script, array, index);
			ReplacementVar repVar = m_ReplacementVarFactory.getOrConstuctReplacementVar(definition);
		return repVar;
	}


	public NestedMap2<TermVariable, ArrayIndex, ArrayCellReplacementVarInformation> getArrayRepresentative2IndexRepresentative2ReplacementVar() {
		return m_ArrayRepresentative2IndexRepresentative2ReplacementVar;
	}
	
	

}
