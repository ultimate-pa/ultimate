package de.uni_freiburg.informatik.ultimate.heapseparator;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
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
	NestedMap2<IProgramVarOrConst, List<EqNode>, ReplacementVar> oldArrayIdToIndexVectorToNewArrayId = 
			new NestedMap2<>();
	
	/**
	 * Stores
	 *  for each original array id and
	 *   for each disjunct index and position in an index vector
	 *    the new array partitions id
	 */
	NestedMap3<IProgramVarOrConst, EqNode, Integer, ReplacementVar> 
		oldArrayIdToDisjunctIndexToPositionToNewArrayId  = 
			new NestedMap3<>();
	
	/**
	 * A disjunct index, wrt. an array, is one that is guaranteed (by the VPDomain's result) to be different from all (non-congruent) 
	 * other indices at each access of the array.
	 * One could also call these indicdes "non-aliasing"
	 */
	HashRelation<IProgramVarOrConst, EqNode> arrayToDisjunctIndices = new HashRelation<>();
	
	Map<IProgramVarOrConst, ReplacementVar> oldArrayToDefaultNewPartition = new HashMap<>();
	
	ReplacementVarFactory mReplacementVarFactory;
	
	public NewArrayIdProvider(ManagedScript ms) {
		mReplacementVarFactory = new ReplacementVarFactory(ms);
	}

	/**
	 * Return the partition id of the partitioned array belonging to originalArrayId at position indexVector
	 * @param originalArrayId
	 * @param indexVector
	 * @return
	 */
	public ReplacementVar getNewArrayId(IProgramVarOrConst originalArrayId, List<EqNode> indexVector) {
		ReplacementVar result = oldArrayIdToIndexVectorToNewArrayId.get(originalArrayId, indexVector);
		
		
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

	private ReplacementVar getNewArrayPartition(IProgramVarOrConst originalArrayId, 
			EqNode disjunctPointer, Integer disjunctPointerIndex) {
		ReplacementVar result = oldArrayIdToDisjunctIndexToPositionToNewArrayId.get(
				originalArrayId, disjunctPointer, disjunctPointerIndex);
		if (result == null) {
			oldArrayIdToDisjunctIndexToPositionToNewArrayId.put(
					originalArrayId, 
					disjunctPointer, 
					disjunctPointerIndex, 
					mReplacementVarFactory.getOrConstuctReplacementVar(originalArrayId.getTerm()));//TODO
		}
		return result;
	}

	private ReplacementVar getDefaultNewId(IProgramVarOrConst originalArrayId) {
		ReplacementVar result = oldArrayToDefaultNewPartition.get(originalArrayId);
		if (result == null) {
			result = mReplacementVarFactory.getOrConstuctReplacementVar(originalArrayId.getTerm());//TODO
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
}
