/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model
 * File:	IAnnotation.java created on Mar 7, 2010 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.model.annotation;

import java.io.Serializable;
import java.util.Map;

/**
 * IAnnotation
 * 
 * @author Björn Buchhold
 * 
 */
public interface IAnnotations extends Serializable {

	/**
	 * Gets the annotations as a string-object mapping for use in output
	 * plug-ins.
	 * 
	 * @return the annotations as string-object mapping
	 */
	Map<String, Object> getAnnotationsAsMap();

}
