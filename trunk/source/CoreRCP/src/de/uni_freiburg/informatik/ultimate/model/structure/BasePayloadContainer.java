package de.uni_freiburg.informatik.ultimate.model.structure;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.Payload;

/***
 * This class is the reference implementation for IElement. It uses the
 * reference implementation for IPayload named Payload.
 * 
 * @author dietsch
 * @see IElement
 * @see Payload
 * 
 */
public abstract class BasePayloadContainer implements IElement {

	/**
	 * ID to distinguish different versions of this class. If the class gains
	 * additional fields, this constant should be incremented. This field may
	 * not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected IPayload mPayload;

	protected BasePayloadContainer() {

	}

	protected BasePayloadContainer(IPayload payload) {
		mPayload = payload;
	}

	@Override
	public IPayload getPayload() {
		if (!this.hasPayload()) {
			mPayload = new Payload();
		}
		return mPayload;
	}

	@Override
	public boolean hasPayload() {
		return mPayload != null;
	}

}
