package de.uni_freiburg.informatik.ultimate.witnessparser.graph;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableMultigraphEdge;

public class WitnessEdge extends ModifiableMultigraphEdge<WitnessNode, WitnessEdge> {

	private static final long serialVersionUID = 1L;
	private final String mName;
	private final String mSourceCode;
	private final WitnessLocation mLocation;

	public WitnessEdge(WitnessNode source, WitnessNode target, String id, WitnessLocation location, String sourcecode) {
		super(source, target);
		mName = id;
		mLocation = location;
		mSourceCode = sourcecode;
		redirectSource(source);
		redirectTarget(target);
	}

	public ILocation getLocation() {
		return mLocation;
	}

	public String getName() {
		return mName;
	}

	public String getSourceCode() {
		return mSourceCode;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		if (mName != null) {
			sb.append("[" + mName + "] ");
		}
		if (mLocation != null) {
			sb.append("L").append(mLocation.getStartLine()).append(" ");
		}
		if (mSourceCode != null) {
			sb.append(mSourceCode);
		}
		return sb.toString();
	}
}