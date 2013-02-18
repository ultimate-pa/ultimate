package local.stalin.model;

import java.io.Serializable;


/**
 * 
 * This interface provides methods for accessing the payload of the STALIN carrier structure. 
 * 
 * @author firefox
 *
 */
public abstract interface IElement extends Serializable {
	
    
    /**
     * Returns the current payload of the node. The payload contains all informations carried by the node.
     * 
     * @return The payload
     */
	IPayload getPayload();
	
	void setPayload(IPayload payload);
	
	boolean hasPayload();
	
//	Flags getFlags();
}
