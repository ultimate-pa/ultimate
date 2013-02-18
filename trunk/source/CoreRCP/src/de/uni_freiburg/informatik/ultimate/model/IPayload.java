package de.uni_freiburg.informatik.ultimate.model;

import java.io.Serializable;
import java.util.HashMap;

/**
 * 
 * This interface describes all information contained in an INode. We use it to
 * hide the data structure from the information and to save resources
 * 
 * @author dietsch
 * 
 */
public interface IPayload extends Serializable {

	/**
	 * Get a two-dimensional HashMap containing Annotations. Initializes
	 * annotations automatically if not already initialized.
	 * 
	 * @return the HashMap containing the annotations
	 */
	HashMap<String, IAnnotations> getAnnotations();

	/**
	 * Sets a two-dimensional HashMap containing Annotations. Do not use to
	 * initialize annotations (use getAnnotation() instead).
	 * 
	 * @param annotations
	 *            the annotations
	 * @deprecated
	 */
	void setAnnotations(HashMap<String, IAnnotations> annotations);

	/**
	 * gets the name of this node, usually the token it represents
	 * 
	 * @deprecated
	 * @return the name
	 */
	String getName();

	/***
	 * 
	 * @deprecated
	 * @param name
	 */
	void setName(String name);

	/**
	 * tries to give you a satisfying answer where this token was found
	 * 
	 * @return the location itself
	 */
	ILocation getLocation();

	/***
	 * 
	 * @deprecated
	 * @param loc
	 */
	void setLocation(ILocation loc);

	/**
	 * Returns the unique identifier for this node. The identifier should be
	 * unique for all objects of the same type.
	 * 
	 * @return A composite data structure serving as unique identifier. Consists
	 *         of a short, long and int.
	 */
	UltimateUID getID();

	/**
	 * Returns true if the annotation hash map is already initialized and
	 * contains elements. Returns false if the annotations are not initialized
	 * or contain no elements. Should be used instead of a direct null test of
	 * the getAnnotations() method to prevent unnecessary initialization.
	 * 
	 * @return true if the annotation hash map is already initialized and
	 *         contains elements. Returns false if the annotations are not
	 *         initialized or contain no elements.
	 */
	boolean hasAnnotation();

	/**
	 * Returns true if the Location Object is already initialized and false if
	 * not. Should be used instead of a direct null test of the getLocation()
	 * method to prevent unnecessary initialization.
	 * 
	 * @return True if the Location has been initialized, false if not
	 */
	boolean hasLocation();

	/**
	 * Returns true if the UltimateUID Object is already initialized and false
	 * if not. Should be used instead of a direct null test of the getID()
	 * method to prevent unnecessary initialization.
	 * 
	 * @return True if the UltimateUID has been initialized, false if not
	 */
	boolean hasID();

	/**
	 * Returns true if the name of the payload is already set and false if not.
	 * Should be used instead of a direct null test of the getName() method to
	 * prevent unnecessary initialization.
	 * 
	 * @deprecated
	 * @return True if the name has been initialized, false if not
	 */
	boolean hasName();

	/**
	 * Returns true if the name of the payload represents a value and false if
	 * not. This method is used to distinguish tokens from real values in case
	 * one our our token keywords equals a value in the original source.
	 * 
	 * @deprecated
	 * @return Returns true if the name of the payload represents a value and
	 *         false if not
	 */
	boolean isValue();
}
