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
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.IndexAnalyzer2.Equality;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;

public class EquivalentCells {
	private final Script m_Script;
	private final UnionFind<TermVariable> m_UnionFind;
	private final Map<TermVariable, TermVariable> m_Representative;
	private final Term m_InOutEqauality;
	private final TransFormulaLR m_TransFormula;
	private final Map<TermVariable, Map<List<Term>, TermVariable>> m_ArrayInstance2Index2CellVariable;
	private final IndexAnalyzer2 m_IndexAnalyzer;

	public EquivalentCells(Script script, TransFormulaLR tf, 
			List<ArrayEquality> arrayEqualities, 
			List<ArrayUpdate> arrayUpdates, IndexAnalyzer2 indexAnalyzer, 
			Map<TermVariable, 
			Map<List<Term>, TermVariable>> arrayInstance2Index2CellVariable) {
		m_Script = script;
		m_TransFormula = tf;
		m_IndexAnalyzer = indexAnalyzer;
		m_ArrayInstance2Index2CellVariable = arrayInstance2Index2CellVariable;
		m_UnionFind = new UnionFind<TermVariable>();
		addArrayIndexConstraints(m_UnionFind);
		addArrayEqualityConstraints(m_UnionFind, arrayEqualities);
		addArrayUpdateConstraints(m_UnionFind, arrayUpdates);
		m_Representative = computeRepresentatives(m_UnionFind);
		m_InOutEqauality = computeInOutEqualities(m_UnionFind);
	}
	
	private void addArrayUpdateConstraints(UnionFind<TermVariable> uf, List<ArrayUpdate> arrayUpdates) {
		for (ArrayUpdate au : arrayUpdates) {
			List<Term> updateIndex = Arrays.asList(au.getIndex());
			Map<List<Term>, TermVariable> newInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(au
					.getNewArray());
			Map<List<Term>, TermVariable> oldInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(au
					.getOldArray());
			for (List<Term> index : newInstance2Index2CellVariable.keySet()) {
				TermVariable newCellVariable = newInstance2Index2CellVariable.get(index);
				TermVariable oldCellVariable = oldInstance2Index2CellVariable.get(index);
				Equality indexEquality = m_IndexAnalyzer.isEqual(index, updateIndex);
				switch (indexEquality) {
				case EQUAL:
					// do nothing
					break;
				case NOT_EQUAL:
					uf.union(newCellVariable, oldCellVariable);
					break;
				case UNKNOWN:
					// do nothing
				default:
					break;
				}
			}
		}
	}

	private void addArrayIndexConstraints(UnionFind<TermVariable> uf) {
		for (Entry<TermVariable, Map<List<Term>, TermVariable>> entry : m_ArrayInstance2Index2CellVariable.entrySet()) {
			Map<List<Term>, TermVariable> indices2values = entry.getValue();
			List<Term>[] indices = new List[indices2values.size()];
			TermVariable[] values = new TermVariable[indices2values.size()];
			int offset = 0;
			for (Entry<List<Term>, TermVariable> index2value : indices2values.entrySet()) {
				indices[offset] = index2value.getKey();
				TermVariable value = index2value.getValue();
				values[offset] = value;
				uf.makeEquivalenceClass(value);
				offset++;
			}
			for (int i = 0; i < indices2values.size(); i++) {
				for (int j = 0; j < i; j++) {
					List<Term> index1 = indices[i];
					List<Term> index2 = indices[j];
					if (m_IndexAnalyzer.isEqual(index1, index2) == Equality.EQUAL) {
						TermVariable value1 = values[i];
						TermVariable value2 = values[j];
						uf.union(value1, value2);
					}
				}
			}
		}

	}

	private void addArrayEqualityConstraints(UnionFind<TermVariable> uf, List<ArrayEquality> arrayEqualities) {
		for (ArrayEquality ae : arrayEqualities) {
			Map<List<Term>, TermVariable> lhsInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(ae
					.getLhs());
			Map<List<Term>, TermVariable> rhsInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(ae
					.getRhs());
			if (lhsInstance2Index2CellVariable == null && rhsInstance2Index2CellVariable == null) {
				// has no index at all
			}
			for (List<Term> index : lhsInstance2Index2CellVariable.keySet()) {
				TermVariable lhsCellVariable = lhsInstance2Index2CellVariable.get(index);
				TermVariable rhsCellVariable = rhsInstance2Index2CellVariable.get(index);
				uf.union(lhsCellVariable, rhsCellVariable);
			}
		}
	}

	private Term computeInOutEqualities(UnionFind<TermVariable> unionFind) {
		List<Term> conjuncts = new ArrayList<Term>();
		for (TermVariable representative : unionFind.getAllRepresentatives()) {
			List<TermVariable> equalInOutVars = new ArrayList<TermVariable>();
			for (TermVariable member : unionFind.getEquivalenceClassMembers(representative)) {
				if (TransFormulaUtils.isInvar(member, m_TransFormula) || TransFormulaUtils.isOutvar(member, m_TransFormula)) {
					equalInOutVars.add(member);
				}
			}
			if (equalInOutVars.size() > 1) {
				Term equality = m_Script.term("=", equalInOutVars.toArray(new Term[equalInOutVars.size()]));
				Term binarized = SmtUtils.binarize(m_Script, (ApplicationTerm) equality);
				conjuncts.add(binarized);
			}
		}
		return Util.and(m_Script, conjuncts.toArray(new Term[conjuncts.size()]));
	}

	private Map<TermVariable, TermVariable> computeRepresentatives(UnionFind<TermVariable> uf) {
		Map<TermVariable, TermVariable> result = new HashMap<TermVariable, TermVariable>();
		for (TermVariable ufRepresentative : uf.getAllRepresentatives()) {
			TermVariable inoutRepresentative = computeInOutRepresentative(uf, ufRepresentative);
			result.put(ufRepresentative, inoutRepresentative);
		}
		return result;
	}

	private TermVariable computeInOutRepresentative(UnionFind<TermVariable> uf, TermVariable ufRepresentative) {
		Set<TermVariable> eq = uf.getEquivalenceClassMembers(ufRepresentative);
		for (TermVariable member : eq) {
			if (TransFormulaUtils.isInvar(member, m_TransFormula) || TransFormulaUtils.isOutvar(member, m_TransFormula)) {
				return member;
			}
		}
		return ufRepresentative;
	}

	public Term getInOutEqauality() {
		return m_InOutEqauality;
	}

	public TermVariable getInOutRepresentative(TermVariable arrayCell) {
		TermVariable ufRepresentative = m_UnionFind.find(arrayCell);
		return m_Representative.get(ufRepresentative);
	}

}
