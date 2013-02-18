/*
* Copyright (c) 2003, the JUNG Project and the Regents of the University 
* of California
* All rights reserved.
*
* This software is open-source under the BSD license; see either
* "license.txt" or
* http://jung.sourceforge.net/license.txt for a description.
*/
package edu.uci.ics.jung.algorithms.layout3d;

import javax.media.j3d.BoundingSphere;
import javax.vecmath.Point3f;

import org.apache.commons.collections15.Transformer;

import edu.uci.ics.jung.graph.Graph;

/**
  * @author tom nelson
 */
public interface Layout<V, E> extends Transformer<V,Point3f> {
    
	/**
	 * Initializes fields in the node that may not have
	 * been set during the constructor. Must be called before
	 * the iterations begin.
	 */
	void initialize();
	
	/**
	 * provides initial locations for all vertices.
	 * @param initializer
	 */
	void setInitializer(Transformer<V,Point3f> initializer);
    
	/**
	 * setter for graph
	 * @param graph
	 */
    void setGraph(Graph<V,E> graph);

	/**
	 * Returns the full graph (the one that was passed in at 
	 * construction time) that this Layout refers to.
	 * 
	 */
	Graph<V,E> getGraph();
	
	/**
	 * 
	 *
	 */
	void reset();
	
	/**
	 * @param d
	 */
	void setSize(BoundingSphere d);
	
	/**
	 * Returns the current size of the visualization's space.
	 */
	BoundingSphere getSize();
	
//	float getWidth();
//	float getHeight();
//	float getDepth();
	
	/**
	 * Sets a flag which fixes this vertex in place.
     * 
	 * @param v	vertex
	 */
	void lock(V v, boolean state);

    /**
     * Returns <code>true</code> if the position of vertex <code>v</code>
     * is locked.
     */
    boolean isLocked(V v);

    /**
     * set the location of a vertex
     * @param v
     * @param location
     */
	void setLocation(V v, Point3f location);


}
