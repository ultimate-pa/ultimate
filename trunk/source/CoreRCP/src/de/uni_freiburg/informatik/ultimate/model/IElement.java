package de.uni_freiburg.informatik.ultimate.model;

import java.io.Serializable;

/**
 * 
 * This interface implements a proxy pattern for IPayload. It is also the root
 * element of the type hierarchy for Ultimate models.
 * 
 * @author dietsch
 * @see IPayload
 */
public interface IElement extends Serializable {

	/**
	 * Returns the current IPayload of the implementation. If this method is
	 * called for the first time, it will initialize a new IPayload object and
	 * return this. All following calls will return the instance that was
	 * created during the first call. In particular, implementers must ensure
	 * that this method never returns null.
	 * 
	 * @return The current IPayload object of the implementation.
	 */
	IPayload getPayload();

	/**
	 * Reports if the IPayload object has been initialized. This method should
	 * be used to check whether a IPayload instance exists if one does not want
	 * to create an instance.
	 * 
	 * @return true iff getPayload() returns an already existing instance of
	 *         IPayload, false iff getPayload() will create a new instance and
	 *         save this, thus increasing memory consumption.
	 */
	boolean hasPayload();
}
