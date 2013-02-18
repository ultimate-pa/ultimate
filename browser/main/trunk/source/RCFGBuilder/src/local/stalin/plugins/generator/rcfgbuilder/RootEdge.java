package local.stalin.plugins.generator.rcfgbuilder;

/**
 * Auxiliary edge from the Root node to the initial LocNodes of a program.
 *    
 * @author heizmann@informatik.uni-freiburg.de
 *
 */

public class RootEdge extends TransEdge {

	private static final long serialVersionUID = -2923506946454722306L;

	public RootEdge(RootNode source, LocNode target) {
		getPayload().setName(" ");
		source.addOutgoingEdge(this);
		this.setSource(source);
		connectTarget(target);
	}

}
