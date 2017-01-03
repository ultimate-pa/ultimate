package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfState;

public class StoreTermWrapper implements IArrayWrapper {

	final IArrayWrapper mBaseArray;

	final List<IElementWrapper> mIndex; // this is a list because the array may be multidimensional

	final IElementWrapper mValue;

	public StoreTermWrapper(IArrayWrapper baseArray, List<IElementWrapper> index, IElementWrapper value) {
		super();
		this.mBaseArray = baseArray;
		this.mIndex = index;
		this.mValue = value;
	}

	@Override
	public Set<ArrayWithSideCondition> getArrayWithSideConditions(VPTfState tfState) {
		Set<ArrayWithSideCondition> result = new HashSet<>();

		/*
		 * Without any (further) sidecondition we know that the value of the storeTerm is at the index
		 * of the storeTerm.
		 * 
		 * technical details:
		 * first we compute the cross product of the results for the elements of the index vector
		 * then one more cross product, with the values
		 * 
		 * for each entry we create an ArrayWithSideCondition
		 * the sidecondition is the conjunction (union) of the sideconditions in the tuple
		 * 
		 */
		List<Set<NodeIdWithSideCondition>> indexNiwscs = mIndex.stream()
				.map(elWr -> elWr.getNodeIdWithSideConditions(tfState))
				.collect(Collectors.toList());
		Set<List<NodeIdWithSideCondition>> combinedIndices = VPDomainHelpers.computeCrossProduct(indexNiwscs);
		
		Set<NodeIdWithSideCondition> valueNiwscs = mValue.getNodeIdWithSideConditions(tfState);
		
		for (List<NodeIdWithSideCondition> indexVector : combinedIndices) {
			Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> indexVectorEqualities = new HashSet<>();
			Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> indexVectorDisEqualities = new HashSet<>();
			for (NodeIdWithSideCondition index : indexVector) {
				indexVectorEqualities.addAll(index.getEqualities());
				indexVectorDisEqualities.addAll(index.getDisEqualities());
				// TODO: might break here if the intersection of both sets is nonempty
			}
			
			for (NodeIdWithSideCondition value : valueNiwscs) {
				Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> resultEqualities = new HashSet<>(indexVectorEqualities);
				Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> resultDisEqualities = new HashSet<>(indexVectorDisEqualities);
				resultEqualities.addAll(value.getEqualities());
				resultDisEqualities.addAll(value.getDisEqualities());

				Map<List<VPTfNodeIdentifier>, VPTfNodeIdentifier> indexToValue = 
						Collections.singletonMap(
								indexVector.stream().map(niwsc -> niwsc.mNodeId).collect(Collectors.toList()),
								value.mNodeId);
				ArrayWithSideCondition storeTermIndexValueAwcs = 
						new ArrayWithSideCondition(indexToValue, resultEqualities, resultDisEqualities);
				result.add(storeTermIndexValueAwcs);
			}
		}
		
		/*
		 * TODO: (?)
		 * the above is only what we can add to result here without adding further sideconditions
		 *  --> we could add much more at the cost of more case splits
		 *  --> the anonymous array only talks about one index position so far, the written one
		 *     (except for case splits introduced in the indices and value..)
		 */


		return result;
	}


}
