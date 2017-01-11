package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfStateBuilder;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class VpTfThroughNodeIdentifier extends VPTfNodeIdentifier {

	/**
	 * @param eqNode
	 * @param tfStateBuilder TODO: parameter seems unnecessary
	 */
	public VpTfThroughNodeIdentifier(EqNode eqNode) {
		super(eqNode);

	}

	@Override
	public VPTfArrayIdentifier getFunction() {
		assert false : "implement this?";
		return null;
	}

	@Override
	public String toString() {
		return "VpTfThroughNodeIdentifier: " + getEqNode().toString();
	}

	@Override
	public boolean equals(Object other) {
		if (!(other instanceof VpTfThroughNodeIdentifier)) {
			return false;
		}

		VpTfThroughNodeIdentifier otherVpThroughId = (VpTfThroughNodeIdentifier) other;
		if (otherVpThroughId.getEqNode() != this.getEqNode()) {
			return false;
		}
		
		return true;
	}

	@Override
	public int hashCode() {
		return HashUtils.hashHsieh(31, getEqNode());
	}
	
	
}
