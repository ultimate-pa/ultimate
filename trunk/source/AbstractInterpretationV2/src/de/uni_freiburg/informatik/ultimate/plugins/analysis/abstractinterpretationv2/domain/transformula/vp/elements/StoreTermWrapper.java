package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Collections;
import java.util.HashMap;
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
	public Set<ArrayWithSideCondition> getArrayWithSideConditions(VPTfState tfState, Set<List<NodeIdWithSideCondition>> requestedIndices) {
		
		
		List<Set<NodeIdWithSideCondition>> indexNiwscs = mIndex.stream()
				.map(elWr -> elWr.getNodeIdWithSideConditions(tfState))
				.collect(Collectors.toList());
		Set<List<NodeIdWithSideCondition>> combinedIndices = VPDomainHelpers.computeCrossProduct(indexNiwscs);

		final Set<NodeIdWithSideCondition> valueNiwscs = mValue.getNodeIdWithSideConditions(tfState);


		/*
		 * Step 1:
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
		Set<ArrayWithSideCondition> resultStep1 = new HashSet<>();
		
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
				resultStep1.add(storeTermIndexValueAwcs);
			}
		}
		
		/*
		 * TODO: (?)
		 * the above is only what we can add to result here without adding further sideconditions
		 *  --> we could add much more at the cost of more case splits
		 *  --> the anonymous array only talks about one index position so far, the written one
		 *     (except for case splits introduced in the indices and value..)
		 */
		
		/*
		 * If we have requested values, we may introduce case splits accordingly; this essentially is 
		 * an application of the select-over-store axioms.
		 * If the index matches the store term's index, we return the store term's value.
		 * Otherwise we return the value for that index from the underlying array.
		 * (yielding two arrays with sideconditions)
		 * 
		 * Note that this is conjunctively connected to the information obtained in Step 1 !! (or more generally: so far?)
		 *  --> we need to adapt the existing AWSCs, not just add new ones.
		 *  
		 * algorithmic plan:
		 *  For each AWSC we already have, we introduce a case split regarding the requested index being equal to the store index.
		 */
		Set<ArrayWithSideCondition> resultStep2 = new HashSet<>();
		if (requestedIndices != null) {
			assert !requestedIndices.isEmpty(); //TODO is there even a use case where requestedIndices is non-null and not a singleton?

			for (List<NodeIdWithSideCondition> reqIndex : requestedIndices) {
				final List<VPTfNodeIdentifier> reqIndexVectorNodeIds = 
						reqIndex.stream().map(niwsc -> niwsc.mNodeId).collect(Collectors.toList());
				Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> reqIndexVectorEqualities = collectEqualities(reqIndex);
				Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> reqIndexVectorDisEqualities = collectDisEqualities(reqIndex);

				for (List<NodeIdWithSideCondition> storeIndex : combinedIndices) {
					final List<VPTfNodeIdentifier> storeIndexVectorNodeIds = 
							storeIndex.stream().map(niwsc -> niwsc.mNodeId).collect(Collectors.toList());
					// the sideconditions of the store index vector should have already been added to the awscs in Step 1
					//  --> we can ignore them here (TODO: perhaps pull out that functionality into a Step 0??)
//					Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> storeIndexVectorEqualities = collectEqualities(storeIndex);
//					Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> storeIndexVectorDisEqualities = collectDisEqualities(storeIndex);
					assert storeIndex.size() == reqIndex.size();

					for (NodeIdWithSideCondition value : valueNiwscs) {
						// the sideconditions of the store value should have already been added to the awscs in Step 1
						//  --> we can ignore them here

						// intuitively the main loop here -> we split each of those awscs in two (if we have one requested index and one store value)
						for (ArrayWithSideCondition awscFromStep1 : resultStep1) { 
							/*
							 * say we have (select (store a i x) j), i.e., j is requested
							 * case 1: i = j
							 */
							{
								final Map<List<VPTfNodeIdentifier>, VPTfNodeIdentifier> newIndexToValue = 
										new HashMap<>(awscFromStep1.mIndexToValue);
								newIndexToValue.put(
										reqIndexVectorNodeIds, 
										value.getNodeId()); // a[j] = x

								Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> newEqualities = 
										new HashSet<>(awscFromStep1.getEqualities());
								newEqualities.addAll(reqIndexVectorEqualities);

								Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> newDisEqualities = 
											new HashSet<>(awscFromStep1.getDisEqualities());
								newDisEqualities.addAll(reqIndexVectorDisEqualities);

								// add "i = j" to the side condition -- i and j are vectors..
								for (int i = 0; i < reqIndexVectorNodeIds.size(); i++) {
									newEqualities.add(
											new VPDomainSymmetricPair<VPTfNodeIdentifier>(
													reqIndexVectorNodeIds.get(i), 
													storeIndexVectorNodeIds.get(i)));
								}

								ArrayWithSideCondition case1awsc = new ArrayWithSideCondition(
										newIndexToValue, newEqualities, newDisEqualities);
								resultStep2.add(case1awsc);
							}

							/*
							 * say we have (select (store a i x) j), i.e., j is requested
							 * case 2: i != j
							 */
							{
								Map<List<VPTfNodeIdentifier>, VPTfNodeIdentifier> newIndexToValue = 
										new HashMap<>(awscFromStep1.mIndexToValue);
								
								// add "i != j" to the side condition -- i and j are vectors.. --> we need a disjunction
								for (int i = 0; i < reqIndex.size(); i++) {
									Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> newEqualities = 
											new HashSet<>(awscFromStep1.getEqualities());
									newEqualities.addAll(reqIndexVectorEqualities);

									Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> newDisEqualities = 
											new HashSet<>(awscFromStep1.getDisEqualities());
									newDisEqualities.addAll(reqIndexVectorDisEqualities);
									newDisEqualities.add(
											new VPDomainSymmetricPair<VPTfNodeIdentifier>(
													reqIndexVectorNodeIds.get(i), 
													storeIndexVectorNodeIds.get(i)));


									ArrayWithSideCondition case2awsc = new ArrayWithSideCondition(
											newIndexToValue, 
											newEqualities,
											newDisEqualities);
									resultStep2.add(case2awsc);
								}
							}
						}
					}
				}
			}
		} else {
			resultStep2 = resultStep1;
		}

		
		
		
		/*
		 * TODO:
		 * We could also leverage the information from tfState to eliminate case splits
		 */

		Set<ArrayWithSideCondition> result = resultStep2;

		return result;
	}

	private Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> collectDisEqualities(
			List<NodeIdWithSideCondition> reqIndex) {
		Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> result = new HashSet<>();
		for (NodeIdWithSideCondition i : reqIndex) {
			result.addAll(i.getDisEqualities());
		}
		return result;

	}

	private Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> collectEqualities(List<NodeIdWithSideCondition> reqIndex) {
		Set<VPDomainSymmetricPair<VPTfNodeIdentifier>> result = new HashSet<>();
		for (NodeIdWithSideCondition i : reqIndex) {
			result.addAll(i.getEqualities());
		}
		return result;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("StoreTermWrapper: ");
		
		sb.append("array: " + mBaseArray.toString());

		sb.append(" index: " + mIndex.toString());

		sb.append(" value: " + mValue.toString());
		
		return sb.toString();
	}

	@Override
	public VPTfArrayIdentifier getBaseArray() {
		return mBaseArray.getBaseArray();
	}
	
}
