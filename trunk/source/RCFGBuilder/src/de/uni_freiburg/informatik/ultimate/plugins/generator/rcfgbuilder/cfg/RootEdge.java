package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import de.uni_freiburg.informatik.ultimate.model.Payload;

/**
 * Auxiliary edge from the Root node to the initial LocNodes of a program.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */

public class RootEdge extends RCFGEdge {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	public RootEdge(RCFGNode source, RCFGNode target) {
		super(source, target, new Payload());
		getPayload().setName(" ");
		setSource(source);
		source.addOutgoing(this);
		setTarget(target);
		target.addIncoming(this);
	}

	@Override
	public String toString() {
		return "RootEdge";
	}

}
