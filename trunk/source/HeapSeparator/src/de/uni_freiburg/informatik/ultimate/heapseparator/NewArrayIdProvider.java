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
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.LocalBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.EqNode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

public class NewArrayIdProvider {
	
//	/**
//	 * maps an original array id and an index vector to a new array id
//	 *  --> caches the "main result" of this class
//	 */
//	NestedMap2<IProgramVarOrConst, List<EqNode>, IProgramVar> oldArrayIdToIndexVectorToNewArrayId = 
//			new NestedMap2<>();
//	
//	/**
//	 * Stores
//	 *  for each original array id and
//	 *   for each disjunct index and position in an index vector
//	 *    the new array partitions id
//	 */
//	NestedMap3<IProgramVarOrConst, IndexPartition, Integer, IProgramVar> 
//		oldArrayIdToIndexPartitionToPositionToNewArrayId  = 
//			new NestedMap3<>();
//	
//	/**
//	 * A disjunct index, wrt. an array, is one that is guaranteed (by the VPDomain's result) to be different from all (non-congruent) 
//	 * other indices at each access of the array.
//	 * One could also call these indicdes "non-aliasing"
//	 */
//	HashRelation<IProgramVarOrConst, IndexPartition> arrayToIndexPartitions = new HashRelation<>();
	
//	Map<IProgramVarOrConst, IProgramVar> oldArrayToDefaultNewPartition = new HashMap<>();
	
	Map<IProgramVarOrConst, PartitionInformation> arrayToPartitionInformation = new HashMap<>();
	private final DefaultIcfgSymbolTable mNewSymbolTable;

	private final ManagedScript mManagedScript;
	private final IIcfgSymbolTable mSymbolTable;
	public NewArrayIdProvider(ManagedScript ms, IIcfgSymbolTable iIcfgSymbolTable) {
		mManagedScript = ms;
		mSymbolTable = iIcfgSymbolTable;
		mNewSymbolTable = new DefaultIcfgSymbolTable((DefaultIcfgSymbolTable) iIcfgSymbolTable);
	}

	/**
	 * Return the partition id of the partitioned array belonging to originalArrayId at position indexVector
	 * @param originalArrayId
	 * @param indexVector
	 * @return
	 */
	public IProgramVarOrConst getNewArrayId(IProgramVarOrConst originalArrayId, List<EqNode> indexVector) {
		return arrayToPartitionInformation.get(originalArrayId).getNewArray(indexVector);
//		IProgramVar result = oldArrayIdToIndexVectorToNewArrayId.get(originalArrayId, indexVector);
//		
//		NestedMap2<IProgramVarOrConst, List<IndexPartition>, IProgramVarOrConst> oldArrayToIndexPartitionsToNewArray
//		  = new NestedMap2<>();
//				
//		
//		if (result == null) {
//			/*
//			 */
//
//			Set<Set<EqNode>> indexPartitions = arrayToIndexPartitions.getImage(originalArrayId);
//			
//			
//			EqNode disjunctPointer = disjunctPointers.iterator().next();
//			Integer disjunctPointerIndex = indexVector.indexOf(disjunctPointer);
//			
//			result = getNewArrayPartition(originalArrayId, disjunctPointer, disjunctPointerIndex);
//		}
//		return null;
	}

//	private IProgramVar getNewArrayPartition(IProgramVarOrConst originalArrayId, 
//			EqNode pointer, Integer argumentPosition) {
//		IProgramVar result = oldArrayIdToIndexPartitionToPositionToNewArrayId.get(
//				originalArrayId, pointer, argumentPosition);
//		if (result == null) {
//			IProgramVar newVariable = obtainFreshProgramVar(originalArrayId);
//			oldArrayIdToIndexPartitionToPositionToNewArrayId.put(
//					originalArrayId, 
//					pointer, 
//					argumentPosition, 
//					newVariable);
//		}
//		return result;
//	}

	

//	private IProgramVar getDefaultNewId(IProgramVarOrConst originalArrayId) {
//		IProgramVar result = oldArrayToDefaultNewPartition.get(originalArrayId);
//		if (result == null) {
//			result = obtainFreshProgramVar(originalArrayId);
//			oldArrayToDefaultNewPartition.put(originalArrayId, result);
//		}
//		return result;
//	}

//	/**
//	 * This must be called for all indices that are known to be disjunct from all other indices
//	 * (except those in the same equivalence class) with respect to array currentArray.
//	 * @param currentArray
//	 * @param ind1
//	 */
//	public void registerDisjunctSinglePointer(IProgramVarOrConst currentArray, EqNode ind1) {
//		arrayToIndexPartitions.addPair(currentArray, ind1);
//	}

	public void registerEquivalenceClass(
			final IProgramVarOrConst arrayId, 
			final Set<EqNode> ec) {
		final IndexPartition indexPartition = new IndexPartition(arrayId, ec);

		PartitionInformation partitionInfo = arrayToPartitionInformation.get(arrayId);
		if (partitionInfo == null) {
			partitionInfo = new PartitionInformation(arrayId, mManagedScript, mNewSymbolTable);
			arrayToPartitionInformation.put(arrayId, partitionInfo);
		}
		partitionInfo.addPartition(indexPartition);
	}
}

/*
 * Represents a set of Array Indices which, with respect to a given array, may never alias with 
 * the indices in any other partition.
 */
class IndexPartition {
	final IProgramVarOrConst arrayId;
	final Set<EqNode> indices;

	public IndexPartition(IProgramVarOrConst arrayId, Set<EqNode> indices) {
		this.arrayId = arrayId;
		this.indices = indices;
	}
}

class PartitionInformation {
	private final IProgramVarOrConst arrayId;
	int versionCounter = 0;
	private final DefaultIcfgSymbolTable mNewSymbolTable;
	private final Set<IndexPartition> indexPartitions;
	
//	final Map<List<EqNode>, IProgramVarOrConst> indexVectorToNewArrayId;
	
	final Map<IndexPartition, IProgramVarOrConst> indexPartitionToNewArrayId = new HashMap<>();
	
	private final Map<List<IndexPartition>, IProgramVarOrConst> partitionVectorToNewArrayId = new HashMap<>();
	
	private final Map<EqNode, IndexPartition> indexToIndexPartition = new HashMap<>();
	private final ManagedScript mManagedScript;
	
	public PartitionInformation(IProgramVarOrConst arrayId, ManagedScript mScript, DefaultIcfgSymbolTable newSymbolTable) {
		this.arrayId = arrayId;
		indexPartitions = new HashSet<>();
		mManagedScript = mScript;
		mNewSymbolTable = newSymbolTable;
	}
	
	public IProgramVarOrConst getNewArray(List<EqNode> indexVector) {
		List<IndexPartition> partitionVector = 
				indexVector.stream().map(eqNode -> indexToIndexPartition.get(eqNode)).collect(Collectors.toList());
		return getNewArrayIdForIndexPartitionVector(partitionVector);
	}

	private IProgramVarOrConst getNewArrayIdForIndexPartitionVector(List<IndexPartition> partitionVector) {
		IProgramVarOrConst result = partitionVectorToNewArrayId.get(partitionVector);
		if (result == null) {
			result = obtainFreshProgramVar(arrayId);
			partitionVectorToNewArrayId.put(partitionVector, arrayId);
		}
		return result;
	}

	void addPartition(IndexPartition ip) {
		indexPartitions.add(ip);
	}

	private int getFreshVersionIndex() {
		//TODO: a method seems overkill right now -- remove if nothing changes..
		return versionCounter++;
	}

	private IProgramVarOrConst obtainFreshProgramVar(IProgramVarOrConst originalArrayId) {
		// TODO: would it be a good idea to introduce something like ReplacementVar for this??
		
		IProgramVarOrConst freshVar = null;
		
		if (originalArrayId instanceof LocalBoogieVar) {
			LocalBoogieVar lbv = (LocalBoogieVar) originalArrayId;
			String newId = lbv.getIdentifier() + "_part_" + getFreshVersionIndex();
			TermVariable newTv = mManagedScript.constructFreshCopy(lbv.getTermVariable());
			ApplicationTerm newConst = (ApplicationTerm) mManagedScript.getScript().term(newId + "_const");
			ApplicationTerm newPrimedConst = (ApplicationTerm) mManagedScript.getScript().term(newId + "_const_primed");
			freshVar = new LocalBoogieVar(
					newId, 
					lbv.getProcedure(), 
					null, 
					newTv, 
					newConst, 
					newPrimedConst);
		} else if (originalArrayId instanceof BoogieNonOldVar) {
			assert false : "TODO: implement";
		} else if (originalArrayId instanceof BoogieOldVar) {
			assert false : "TODO: implement";
		} else if (originalArrayId instanceof ReplacementVar) {
			assert false : "TODO: implement";
		} else if (originalArrayId instanceof BoogieConst) {
			assert false : "TODO: implement";
		} else {
			assert false : "case missing --> add it?";
		}
		
		mNewSymbolTable.add(freshVar);
		return freshVar;
	}
}
