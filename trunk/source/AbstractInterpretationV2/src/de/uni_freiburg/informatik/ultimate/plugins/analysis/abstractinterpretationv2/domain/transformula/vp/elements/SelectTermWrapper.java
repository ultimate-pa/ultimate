package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfState;

public class SelectTermWrapper implements IElementWrapper {
	
	IArrayWrapper mArray;

	List<IElementWrapper> mIndices; // this is a list because we may have a multidimensional array

	public SelectTermWrapper(IArrayWrapper array, List<IElementWrapper> indices) {
		this.mArray = array;
		this.mIndices = indices;
	}

	@Override
	public Set<NodeIdWithSideCondition> getNodeIdWithSideConditions(VPTfState tfState) {
		

		List<Set<NodeIdWithSideCondition>> indexNiwscs = mIndices.stream()
				.map(elWr -> elWr.getNodeIdWithSideConditions(tfState))
				.collect(Collectors.toList());
		Set<List<NodeIdWithSideCondition>> combinedIndices = VPDomainHelpers.computeCrossProduct(indexNiwscs);

		Set<ArrayWithSideCondition> arrayWscs = mArray.getArrayWithSideConditions(tfState, combinedIndices);	

		Set<NodeIdWithSideCondition> result = new HashSet<>();

		for (ArrayWithSideCondition arrayWsc : arrayWscs) {
			for (List<NodeIdWithSideCondition> indexVector : combinedIndices) {
				
				List<VPTfNodeIdentifier> indexVectorAsNodeIds = 
						indexVector.stream().map(niwsc -> niwsc.mNodeId).collect(Collectors.toList());
				
				VPTfNodeIdentifier valueAtIndex = arrayWsc.getIndexToValue().get(indexVectorAsNodeIds);
				
				// compute the new side condition
				Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> resultEqualities = 
						new HashSet<>(arrayWsc.getEqualities());
				Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> resultDisEqualities = 
						new HashSet<>(arrayWsc.getDisEqualities());
				for (NodeIdWithSideCondition i : indexVector) {
					resultEqualities.addAll(i.getEqualities());
					resultDisEqualities.addAll(i.getDisEqualities());
				}
				// TODO filter out inconsistent nodes (i.e. with contradicting side conditions)
				
				if (valueAtIndex != null) {
					// the arrayWsc gives us a value for the given index --> return that
					result.add(
							new NodeIdWithSideCondition(
									valueAtIndex, 
									resultEqualities, 
									resultDisEqualities));
				} else {
					// we don't know the array's value at the given index
					// --> we can still return the condition under which the index is indeterminate
					assert !resultEqualities.isEmpty() || !resultDisEqualities.isEmpty() : "would this be equivalent to adding nothing??";
					result.add(
							new UndetermindedNodeWithSideCondition(
									resultEqualities, 
									resultDisEqualities));
				}
			}
		}
		
		assert !result.isEmpty();
		return result;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("SelectTermWrapper:");
		
		sb.append(" array: " + mArray.toString());

		sb.append(" index: " + mIndices.toString());
		
		return sb.toString();
	}
}
