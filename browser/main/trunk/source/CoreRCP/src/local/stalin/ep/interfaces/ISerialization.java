package local.stalin.ep.interfaces;

import local.stalin.model.IElement;

/**
 * This is a base interface for Stalin serialization plugins 
 * 
 * @author Justus
 * @since 359
 * 
 *  $LastChangedRevision: 517 $
 *  $LastChangedDate: 2008-05-28 14:45:36 +0200 (Mi, 28. Mai 2008) $
 *  $LastChangedBy: dietsch $
 *
 */
public interface ISerialization extends IRCPPlugin{
	
	/**
	 * This is the method to save an element to a location
	 * given in a String
	 * 
	 * @param node the IElement to save
	 * @param location where to save
	 */
	public void serialize(IElement node, String location);
	
	/**
	 * This is a method to load an IElement from a location
	 * 
	 * @param location
	 * @return the deserialized IElement
	 */
	public IElement deserialize(String location);
}
