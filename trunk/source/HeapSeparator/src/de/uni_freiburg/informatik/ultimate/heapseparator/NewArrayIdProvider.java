/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE HeapSeparator plug-in.
 *
 * The ULTIMATE HeapSeparator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE HeapSeparator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE HeapSeparator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE HeapSeparator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE HeapSeparator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.heapseparator;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.EqNode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

public class NewArrayIdProvider {
	
	/**
	 * maps an original array id and an index vector to a new array id
	 *  --> caches the "main result" of this class
	 */
	NestedMap2<IProgramVarOrConst, List<EqNode>, IProgramVar> oldArrayIdToIndexVectorToNewArrayId = 
			new NestedMap2<>();
	
	/**
	 * Stores
	 *  for each original array id and
	 *   for each disjunct index and position in an index vector
	 *    the new array partitions id
	 */
	NestedMap3<IProgramVarOrConst, EqNode, Integer, IProgramVar> 
		oldArrayIdToDisjunctIndexToPositionToNewArrayId  = 
			new NestedMap3<>();
	
	/**
	 * A disjunct index, wrt. an array, is one that is guaranteed (by the VPDomain's result) to be different from all (non-congruent) 
	 * other indices at each access of the array.
	 * One could also call these indicdes "non-aliasing"
	 */
	HashRelation<IProgramVarOrConst, EqNode> arrayToDisjunctIndices = new HashRelation<>();
	
	Map<IProgramVarOrConst, IProgramVar> oldArrayToDefaultNewPartition = new HashMap<>();

	private final ManagedScript mManagedScript;
	
	public NewArrayIdProvider(ManagedScript ms) {
		mManagedScript = ms;
	}

	/**
	 * Return the partition id of the partitioned array belonging to originalArrayId at position indexVector
	 * @param originalArrayId
	 * @param indexVector
	 * @return
	 */
	public IProgramVar getNewArrayId(IProgramVarOrConst originalArrayId, List<EqNode> indexVector) {
		IProgramVar result = oldArrayIdToIndexVectorToNewArrayId.get(originalArrayId, indexVector);
		
		
		if (result == null) {
			/*
			 * Our convention on index-vectors:
			 * If a vector contains at least one disjunct single pointer, it gets its own array partition.
			 */
			Set<EqNode> disjunctPointers = new HashSet<>(arrayToDisjunctIndices.getImage(originalArrayId));
			disjunctPointers.retainAll(indexVector);
			
			if (disjunctPointers.isEmpty()) {
				return getDefaultNewId(originalArrayId);
			}
			
			EqNode disjunctPointer = disjunctPointers.iterator().next();
			Integer disjunctPointerIndex = indexVector.indexOf(disjunctPointer);
			
			result = getNewArrayPartition(originalArrayId, disjunctPointer, disjunctPointerIndex);
		}
		return null;
	}

	private IProgramVar getNewArrayPartition(IProgramVarOrConst originalArrayId, 
			EqNode disjunctPointer, Integer disjunctPointerIndex) {
		IProgramVar result = oldArrayIdToDisjunctIndexToPositionToNewArrayId.get(
				originalArrayId, disjunctPointer, disjunctPointerIndex);
		if (result == null) {

			IProgramVar newVariable = obtainFreshProgramVar(originalArrayId);
			oldArrayIdToDisjunctIndexToPositionToNewArrayId.put(
					originalArrayId, 
					disjunctPointer, 
					disjunctPointerIndex, 
					newVariable);
		}
		return result;
	}

	private IProgramVar obtainFreshProgramVar(IProgramVarOrConst originalArrayId) {
		//TOOD rework with the new symbolTable (i would hope that it will provide a method similar to Boogie2SMTsymboltable
		// that constructs a ProgramVar
		TermVariable newTv = mManagedScript.constructFreshCopy((TermVariable) originalArrayId.getTerm());
		IProgramVar result = new BoogieNonOldVar(newTv.getName(), null, newTv, null, null, null);
		return result;
	}

	private IProgramVar getDefaultNewId(IProgramVarOrConst originalArrayId) {
		IProgramVar result = oldArrayToDefaultNewPartition.get(originalArrayId);
		if (result == null) {
			result = obtainFreshProgramVar(originalArrayId);
			oldArrayToDefaultNewPartition.put(originalArrayId, result);
		}
		return result;
	}

	/**
	 * This must be called for all indices that are known to be disjunct from all other indices
	 * (except those in the same equivalence class) with respect to array currentArray.
	 * @param currentArray
	 * @param ind1
	 */
	public void registerDisjunctSinglePointer(IProgramVarOrConst currentArray, EqNode ind1) {
		arrayToDisjunctIndices.addPair(currentArray, ind1);
	}

	public void registerEquivalenceClass(IProgramVarOrConst currentArray, Set<EqNode> ec) {
		// TODO Auto-generated method stub
		
	}
}
