/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis.IndexAnalysisResult;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class EquivalentCells {
	private final Script mScript;
	private final UnionFind<TermVariable> mUnionFind;
	private final Map<TermVariable, TermVariable> mRepresentative;
	private final Term mInOutEqauality;
	private final ModifiableTransFormula mTransFormula;
	private final Map<TermVariable, Map<ArrayIndex, TermVariable>> mArrayInstance2Index2CellVariable;
	private final IndexAnalysisResult mIndexAnalyzer;

	public EquivalentCells(final Script script, final ModifiableTransFormula tf, 
			final List<ArrayEquality> arrayEqualities, 
			final List<ArrayUpdate> arrayUpdates, final IndexAnalysisResult indexAnalyzer, 
			final Map<TermVariable, 
			Map<ArrayIndex, TermVariable>> arrayInstance2Index2CellVariable) {
		mScript = script;
		mTransFormula = tf;
		mIndexAnalyzer = indexAnalyzer;
		mArrayInstance2Index2CellVariable = arrayInstance2Index2CellVariable;
		mUnionFind = new UnionFind<TermVariable>();
		addArrayIndexConstraints(mUnionFind);
		addArrayEqualityConstraints(mUnionFind, arrayEqualities);
		addArrayUpdateConstraints(mUnionFind, arrayUpdates);
		mRepresentative = computeRepresentatives(mUnionFind);
		mInOutEqauality = computeInOutEqualities(mUnionFind);
	}
	
	private void addArrayUpdateConstraints(final UnionFind<TermVariable> uf, final List<ArrayUpdate> arrayUpdates) {
		for (final ArrayUpdate au : arrayUpdates) {
			final List<Term> updateIndex = au.getIndex();
			final Map<ArrayIndex, TermVariable> newInstance2Index2CellVariable = mArrayInstance2Index2CellVariable.get(au
					.getNewArray());
			final Map<ArrayIndex, TermVariable> oldInstance2Index2CellVariable = mArrayInstance2Index2CellVariable.get(au
					.getOldArray());
			for (final ArrayIndex index : newInstance2Index2CellVariable.keySet()) {
				final TermVariable newCellVariable = newInstance2Index2CellVariable.get(index);
				final TermVariable oldCellVariable = oldInstance2Index2CellVariable.get(index);
				final EqualityStatus indexEquality = mIndexAnalyzer.isEqual(index, updateIndex);
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

	private void addArrayIndexConstraints(final UnionFind<TermVariable> uf) {
		for (final Entry<TermVariable, Map<ArrayIndex, TermVariable>> entry : mArrayInstance2Index2CellVariable.entrySet()) {
			final Map<ArrayIndex, TermVariable> indices2values = entry.getValue();
			final List<Term>[] indices = new List[indices2values.size()];
			final TermVariable[] values = new TermVariable[indices2values.size()];
			int offset = 0;
			for (final Entry<ArrayIndex, TermVariable> index2value : indices2values.entrySet()) {
				indices[offset] = index2value.getKey();
				final TermVariable value = index2value.getValue();
				values[offset] = value;
				uf.makeEquivalenceClass(value);
				offset++;
			}
			for (int i = 0; i < indices2values.size(); i++) {
				for (int j = 0; j < i; j++) {
					final List<Term> index1 = indices[i];
					final List<Term> index2 = indices[j];
					if (mIndexAnalyzer.isEqual(index1, index2) == EqualityStatus.EQUAL) {
						final TermVariable value1 = values[i];
						final TermVariable value2 = values[j];
						uf.union(value1, value2);
					}
				}
			}
		}

	}

	private void addArrayEqualityConstraints(final UnionFind<TermVariable> uf, final List<ArrayEquality> arrayEqualities) {
		for (final ArrayEquality ae : arrayEqualities) {
			final Map<ArrayIndex, TermVariable> lhsInstance2Index2CellVariable = mArrayInstance2Index2CellVariable.get(ae
					.getLhsTermVariable());
			final Map<ArrayIndex, TermVariable> rhsInstance2Index2CellVariable = mArrayInstance2Index2CellVariable.get(ae
					.getRhsTermVariable());
			if (lhsInstance2Index2CellVariable == null && rhsInstance2Index2CellVariable == null) {
				// has no index at all
			}
			for (final List<Term> index : lhsInstance2Index2CellVariable.keySet()) {
				final TermVariable lhsCellVariable = lhsInstance2Index2CellVariable.get(index);
				assert lhsCellVariable != null : "no cell variable for " + index;
				final TermVariable rhsCellVariable = rhsInstance2Index2CellVariable.get(index);
				assert rhsCellVariable != null : "no cell variable for " + index;
				uf.union(lhsCellVariable, rhsCellVariable);
			}
		}
	}

	private Term computeInOutEqualities(final UnionFind<TermVariable> unionFind) {
		final List<Term> conjuncts = new ArrayList<Term>();
		for (final TermVariable representative : unionFind.getAllRepresentatives()) {
			final List<TermVariable> equalInOutVars = new ArrayList<TermVariable>();
			for (final TermVariable member : unionFind.getEquivalenceClassMembers(representative)) {
				if (ModifiableTransFormulaUtils.isInvar(member, mTransFormula) || ModifiableTransFormulaUtils.isOutvar(member, mTransFormula)) {
					equalInOutVars.add(member);
				}
			}
			if (equalInOutVars.size() > 1) {
				final Term equality = mScript.term("=", equalInOutVars.toArray(new Term[equalInOutVars.size()]));
				final Term binarized = SmtUtils.binarize(mScript, (ApplicationTerm) equality);
				conjuncts.add(binarized);
			}
		}
		return SmtUtils.and(mScript, conjuncts.toArray(new Term[conjuncts.size()]));
	}

	private Map<TermVariable, TermVariable> computeRepresentatives(final UnionFind<TermVariable> uf) {
		final Map<TermVariable, TermVariable> result = new HashMap<TermVariable, TermVariable>();
		for (final TermVariable ufRepresentative : uf.getAllRepresentatives()) {
			final TermVariable inoutRepresentative = computeInOutRepresentative(uf, ufRepresentative);
			result.put(ufRepresentative, inoutRepresentative);
		}
		return result;
	}

	private TermVariable computeInOutRepresentative(final UnionFind<TermVariable> uf, final TermVariable ufRepresentative) {
		final Set<TermVariable> eq = uf.getEquivalenceClassMembers(ufRepresentative);
		for (final TermVariable member : eq) {
			if (ModifiableTransFormulaUtils.isInvar(member, mTransFormula) || ModifiableTransFormulaUtils.isOutvar(member, mTransFormula)) {
				return member;
			}
		}
		return ufRepresentative;
	}

	public Term getInOutEqauality() {
		return mInOutEqauality;
	}

	public TermVariable getInOutRepresentative(final TermVariable arrayCell) {
		final TermVariable ufRepresentative = mUnionFind.find(arrayCell);
		return mRepresentative.get(ufRepresentative);
	}

}
