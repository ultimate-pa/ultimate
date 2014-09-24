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
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Object for storing information about an array cell for which we will
 * construct a replacement var.
 * @author Matthias Heizmann
 *
 */
public class ArrayCellReplacementVarInformation {
	
	public enum VarType { InVar, OutVar };
	/**
	 * Array that occurs in the formula
	 */
	private final TermVariable m_ArrayInstance;
	/**
	 * Representative of the BoogieVar for the corresponding array.
	 */
	private final TermVariable m_ArrayRepresentative;
	/**
	 * Index as it occurs in the formula.
	 */
	private final List<Term> m_Index;
	/**
	 * Index in which each TermVariable is translated to the representative
	 * of the corresponding BoogieVar.
	 */
	private final List<Term> m_IndexRepresentative;
	private final VarType m_VarType;
	
	/**
	 * TransFormula in which arrayInstance and index occurred.
	 */
	private final TransFormulaLR m_TransFormulaLR;
	
	private ReplacementVar m_ReplacementVar;
	
	
	public ArrayCellReplacementVarInformation(TermVariable arrayInstance,
			TermVariable arrayRepresentative, List<Term> index,
			List<Term> indexRepresentative, VarType varType, TransFormulaLR transFormulaLR) {
		super();
		m_ArrayInstance = arrayInstance;
		m_ArrayRepresentative = arrayRepresentative;
		m_Index = index;
		m_IndexRepresentative = indexRepresentative;
		m_VarType = varType;
		m_TransFormulaLR = transFormulaLR;
	}


	public TermVariable getArrayInstance() {
		return m_ArrayInstance;
	}


	public TermVariable getArrayRepresentative() {
		return m_ArrayRepresentative;
	}


	public List<Term> getIndex() {
		return m_Index;
	}


	public List<Term> getIndexRepresentative() {
		return m_IndexRepresentative;
	}


	public VarType getVarType() {
		return m_VarType;
	}


	public ReplacementVar getReplacementVar() {
		return m_ReplacementVar;
	}


	public void setReplacementVar(ReplacementVar replacementVar) {
		m_ReplacementVar = replacementVar;
	}
	
	
	public Map<TermVariable, RankVar> termVariableToRankVarMappingForIndex() {
		Map<TermVariable, RankVar> result = new HashMap<TermVariable, RankVar>();
		for (Term entry : m_Index) {
			for (TermVariable tv : entry.getFreeVars()) {
				RankVar inVar = m_TransFormulaLR.getInVarsReverseMapping().get(tv);
				if (inVar != null) {
					result.put(tv, inVar);
				} else {
					RankVar outVar = m_TransFormulaLR.getInVarsReverseMapping().get(tv);
					if (outVar != null) {
						result.put(tv, outVar);
					} else {
						throw new AssertionError("must be an auxVar!?! rare case, not yet implemented");
					}
				}
			}
		}
		return result;
	}
	
	public RankVar getArrayRankVar() {
		return m_TransFormulaLR.getInVarsReverseMapping().get(m_ArrayInstance);
	}
	
}
