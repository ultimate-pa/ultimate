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

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.IReplacementVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
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
	private final TermVariable mArrayInstance;
	/**
	 * Representative of the BoogieVar for the corresponding array.
	 */
	private final TermVariable mArrayRepresentative;
	/**
	 * Index as it occurs in the formula.
	 */
	private final ArrayIndex mIndex;
	/**
	 * Index in which each TermVariable is translated to the representative
	 * of the corresponding BoogieVar.
	 */
	private final ArrayIndex mIndexRepresentative;
	private final VarType mVarType;
	
	/**
	 * TransFormula in which arrayInstance and index occurred.
	 */
	private final ModifiableTransFormula mTransFormulaLR;
	
	private IReplacementVarOrConst mReplacementVar;
	
	
	public ArrayCellReplacementVarInformation(TermVariable arrayInstance,
			TermVariable arrayRepresentative, ArrayIndex index,
			ArrayIndex indexRepresentative, VarType varType, ModifiableTransFormula transFormulaLR) {
		super();
		mArrayInstance = arrayInstance;
		mArrayRepresentative = arrayRepresentative;
		mIndex = index;
		mIndexRepresentative = indexRepresentative;
		mVarType = varType;
		mTransFormulaLR = transFormulaLR;
	}


	public TermVariable getArrayInstance() {
		return mArrayInstance;
	}


	public TermVariable getArrayRepresentative() {
		return mArrayRepresentative;
	}


	public ArrayIndex getIndex() {
		return mIndex;
	}


	public ArrayIndex getIndexRepresentative() {
		return mIndexRepresentative;
	}


	public VarType getVarType() {
		return mVarType;
	}


	public IReplacementVarOrConst getReplacementVar() {
		return mReplacementVar;
	}


	public void setReplacementVar(IReplacementVarOrConst replacementVar) {
		mReplacementVar = replacementVar;
	}
	
	
	public Map<TermVariable, IProgramVar> termVariableToRankVarMappingForIndex() {
		final Map<TermVariable, IProgramVar> result = new HashMap<TermVariable, IProgramVar>();
		for (final Term entry : mIndex) {
			for (final TermVariable tv : entry.getFreeVars()) {
				final IProgramVar inVar = mTransFormulaLR.getInVarsReverseMapping().get(tv);
				if (inVar != null) {
					result.put(tv, inVar);
				} else {
					final IProgramVar outVar = mTransFormulaLR.getOutVarsReverseMapping().get(tv);
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
	
	public IProgramVar getArrayRankVar() {
		IProgramVar result = mTransFormulaLR.getInVarsReverseMapping().get(mArrayInstance);
		if (result == null) {
			result = mTransFormulaLR.getOutVarsReverseMapping().get(mArrayInstance);
		}
		if (result == null) {
			throw new AssertionError("unknown array cell");
		}
		return result;
	}
	
}
