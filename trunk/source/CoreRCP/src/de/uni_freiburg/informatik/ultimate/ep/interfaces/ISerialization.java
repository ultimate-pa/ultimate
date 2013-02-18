package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * This is a base interface for Ultimate serialization plugins 
 * 
 * @author Justus
 * @since 359
 * 
 *  $LastChangedRevision$
 *  $LastChangedDate$
 *  $LastChangedBy$
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
