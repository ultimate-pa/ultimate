package local.stalin.plugins.generator.rcfgbuilder;


/**
 * Represents an edge without any effect to the programs variables.
 * While constructing the CFG of a Boogie program these edges are used
 * temporarily but do not occur in the result.
 *    
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class GotoEdge extends TransEdge {

	private static final long serialVersionUID = -2923506946454722306L;

	public GotoEdge(LocNode source, LocNode target) {
		getPayload().setName("goto");
		connectSource(source);
		connectTarget(target);
	}

}
