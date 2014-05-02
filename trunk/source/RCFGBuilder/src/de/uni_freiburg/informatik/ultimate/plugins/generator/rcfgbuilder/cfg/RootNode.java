package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;

/**
 * Root node in a Ultimate Model of a program. Information about about the
 * program represented by this Ultimate Model which can not be expressed by the
 * recursive control flow graph are stored in a RootAnnot object stored in the
 * Payload of this RootNode.
 * The ILocation of the RootNode should be the ILocation of the unit of a
 * Boogie Program.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class RootNode extends RCFGNode {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	public RootNode(ILocation location, RootAnnot rootAnnot) {
		super(new Payload(location, "RootNode"));
		getPayload().getAnnotations().put(Activator.PLUGIN_ID, rootAnnot);
	}

	public RootAnnot getRootAnnot() {
		return ((RootAnnot) getPayload().getAnnotations().get(
				Activator.PLUGIN_ID));
	}

	@Override
	public boolean addIncoming(RCFGEdge incoming) {
		throw new UnsupportedOperationException(
				"RootNode has no incoming edges");
	}

	@Override
	public String toString() {
		return getPayload().getName();
	}
}
