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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfState;


/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class SelectTermWrapper implements IElementWrapper {
	
	IArrayWrapper mArray;

	List<IElementWrapper> mIndices; // this is a list because we may have a multidimensional array

	public SelectTermWrapper(IArrayWrapper array, List<IElementWrapper> indices) {
		this.mArray = array;
		this.mIndices = indices;
	}

	@Override
	public Set<NodeIdWithSideCondition> getNodeIdWithSideConditions(VPTfState tfState) {
		

		final List<Set<NodeIdWithSideCondition>> indexNiwscs = mIndices.stream()
				.map(elWr -> elWr.getNodeIdWithSideConditions(tfState))
				.collect(Collectors.toList());
		final Set<List<NodeIdWithSideCondition>> combinedIndices = VPDomainHelpers.computeCrossProduct(indexNiwscs);

		final Set<ArrayWithSideCondition> arrayWscs = mArray.getArrayWithSideConditions(tfState, combinedIndices);	

		final Set<NodeIdWithSideCondition> result = new HashSet<>();

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
							new UndeterminedNodeWithSideCondition(
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
