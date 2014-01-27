package de.uni_freiburg.informatik.ultimate.model.structure;

import de.uni_freiburg.informatik.ultimate.model.IPayload;

/***
 * 
 * This class is a leftover from the old data structures of Ultimate.
 * 
 * It is still used by some plugins, but should not be used in any new plugins.
 * 
 * @author dietsch
 * 
 */
public class WrapperNode extends ModifiableAST<WrapperNode> {
	private static final long serialVersionUID = 203486790200450017L;
	private Object mBacking;

	public WrapperNode(WrapperNode parent, Object backing) {
		this(parent, backing, null);
	}

	public WrapperNode(WrapperNode parent, Object backing, IPayload payload) {
		super(parent, payload);
		this.mBacking = backing;
	}

	public Object getBacking() {
		return mBacking;
	}
	
	@Override
	public String toString() {
		if (mBacking != null) {
			return mBacking.toString();
		}
		return "NoBacking";
	}
}
