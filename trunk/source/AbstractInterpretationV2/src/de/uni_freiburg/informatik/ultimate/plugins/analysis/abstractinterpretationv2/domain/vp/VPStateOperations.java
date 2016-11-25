package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class VPStateOperations {
	
	public static Set<VPState> addDisEquality(EqGraphNode n1, EqGraphNode n2, VPState originalState) {

		Set<VPState> result = new HashSet<>();
		
		Set<VPState> bottom = new HashSet<>();
		bottom.add(originalState.getDomain().getBottomState());
		
		if (originalState.find(n1).equals(originalState.find(n2))) {
			return bottom;
		}
		originalState.addToDisEqSet(n1, n2);
		
		Set<List<EqGraphNode>> ccchild1 = originalState.ccchild(n1);
		Set<List<EqGraphNode>> ccchild2 = originalState.ccchild(n2);
		
		List<VPState> stateList = new ArrayList<>();
		
		// propagation of disequality
		for (int i = 0; i < ((EqFunctionNode)n1.eqNode).getArgs().size(); i++) {
			VPState newState = originalState.copy();
			stateList.addAll(addDisEquality(n1.getInitCcchild().get(i), n2.getInitCcchild().get(i), newState));
		}
		

		return result;
		
	}
	
	
	public VPState checkContradiction(VPState state) {

		for (final VPDomainSymmetricPair<EqGraphNode> disEqPair : state.getDisEqualitySet()) {
			if (state.find(disEqPair.getFirst()).equals(state.find(disEqPair.getSecond()))) {
				return state.getDomain().getBottomState();
			}
		}
		return state;
	}
	
}
