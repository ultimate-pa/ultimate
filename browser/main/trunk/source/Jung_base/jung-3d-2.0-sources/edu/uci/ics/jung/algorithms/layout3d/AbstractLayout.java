/*
 * Copyright (c) 2003, the JUNG Project and the Regents of the University of
 * California All rights reserved.
 * 
 * This software is open-source under the BSD license; see either "license.txt"
 * or http://jung.sourceforge.net/license.txt for a description.
 * 
 * Created on Jul 7, 2003
 * 
 */
package edu.uci.ics.jung.algorithms.layout3d;

import java.util.Collection;
import java.util.ConcurrentModificationException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import javax.media.j3d.BoundingSphere;
import javax.vecmath.Point3f;

import org.apache.commons.collections15.Transformer;
import org.apache.commons.collections15.map.LazyMap;

import edu.uci.ics.jung.graph.Graph;

/**
 * Implements some of the dirty work of writing a layout algorithm, allowing
 * the user to express their major intent more simply. When writing a <tt>Layout</tt>,
 * there are many shared tasks: handling tracking locked nodes, applying
 * filters, and tracing nearby vertices. This package automates all of those.
 * 
 * @author Danyel Fisher, Scott White
 * @param <V>
 */
public abstract class AbstractLayout<V, E> implements Layout<V,E> {

    /**
     * a set of vertices that should not move in relation to the
     * other vertices
     */
	private Set<V> dontmove = new HashSet<V>();

	private BoundingSphere size;
	private Graph<V, E> graph;
    
    protected Map<V, Point3f> locations = 
    	LazyMap.decorate(new HashMap<V, Point3f>(),
    			new Transformer<V,Point3f>() {
					public Point3f transform(V arg0) {
						return new Point3f();
					}});


	/**
	 * Constructor. Initializes the current size to be 100x100, both the graph
	 * and the showing graph to the argument, and creates the <tt>dontmove</tt>
	 * set.
	 * 
	 * @param g
	 */
	protected AbstractLayout(Graph<V, E> graph) {
		this.graph = graph;
	}
	
	protected AbstractLayout(Graph<V,E> graph, Transformer<V,Point3f> initializer) {
		this.graph = graph;
		this.locations = LazyMap.decorate(new HashMap<V,Point3f>(), initializer);
	}
	
	protected AbstractLayout(Graph<V,E> graph, BoundingSphere size) {
		this.graph = graph;
		this.size = size;
	}
	
	protected AbstractLayout(Graph<V,E> graph, Transformer<V,Point3f> initializer, BoundingSphere size) {
		this.graph = graph;
		this.locations = LazyMap.decorate(new HashMap<V,Point3f>(), initializer);
		this.size = size;
	}
    
    public void setGraph(Graph<V,E> graph) {
        this.graph = graph;
        if(size != null && graph != null) {
        	initialize();
        }
    }
    
	/**
	 * When a visualization is resized, it presumably wants to fix the
	 * locations of the vertices and possibly to reinitialize its data. The
	 * current method calls <tt>initializeLocations</tt> followed by <tt>initialize_local</tt>.
	 * TODO: A better implementation wouldn't destroy the current information,
	 * but would either scale the current visualization, or move the nodes
	 * toward the new center.
	 */
	public void setSize(BoundingSphere size) {
		
		if(size != null && graph != null) {
			
			BoundingSphere oldSize = this.size;
			this.size = size;
			initialize();
			
			if(oldSize != null) {
				adjustLocations(oldSize, size);
			}
		}
	}
	
	private void adjustLocations(BoundingSphere oldSize, BoundingSphere size) {
		
		float oldWidth = 0;
		float oldHeight = 0;
		float oldDepth = 0;
		float width = 0;
		float height = 0;
		float depth = 0;
		
		oldWidth = oldHeight = oldDepth = (float) (2*oldSize.getRadius());
		width = height = depth = (float) (2*size.getRadius());

		float xOffset = (oldWidth - width) / 2;
		float yOffset = (oldHeight - height) / 2;
		float zOffset = (oldDepth - depth) / 2;

		// now, move each vertex to be at the new screen center
		while(true) {
		    try {
                for(V v : getGraph().getVertices()) {
		            offsetVertex(v, xOffset, yOffset, zOffset);
		        }
		        break;
		    } catch(ConcurrentModificationException cme) {
		    }
		}
	}
    
    public boolean isLocked(V v) {
        return dontmove.contains(v);
    }

    public Collection<V> getVertices() {
    	return getGraph().getVertices();
    }
    
	/**
	 * Initializer, calls <tt>intialize_local</tt> and <tt>initializeLocations</tt>
	 * to start construction process.
	 */
	public abstract void initialize();

    public void setInitializer(Transformer<V,Point3f> initializer) {
    	this.locations = LazyMap.decorate(new HashMap<V,Point3f>(locations), initializer);
    }
    
	/**
	 * Returns the current size of the visualization space, accoring to the
	 * last call to resize().
	 * 
	 * @return the current size of the screen
	 */
	public BoundingSphere getSize() {
		return size;
	}

	/**
	 * Returns the Coordinates object that stores the vertex' x and y location.
	 * 
	 * @param v
	 *            A Vertex that is a part of the Graph being visualized.
	 * @return A Coordinates object with x and y locations.
	 */
	private Point3f getCoordinates(V v) {
        return locations.get(v);
	}
	
	public Point3f transform(V v) {
		return getCoordinates(v);
	}
	
	/**
	 * Returns the x coordinate of the vertex from the Coordinates object.
	 * in most cases you will be better off calling getLocation(Vertex v);
	 * @see edu.uci.ics.jung.visualization.layout.Layout#getX(edu.uci.ics.jung.graph.Vertex)
	 */
	public double getX(V v) {
        assert getCoordinates(v) != null : "Cannot getX for an unmapped vertex "+v;
        return getCoordinates(v).getX();
	}

	/**
	 * Returns the y coordinate of the vertex from the Coordinates object.
	 * In most cases you will be better off calling getLocation(Vertex v)
	 * @see edu.uci.ics.jung.visualization.layout.Layout#getX(edu.uci.ics.jung.graph.Vertex)
	 */
	public double getY(V v) {
        assert getCoordinates(v) != null : "Cannot getY for an unmapped vertex "+v;
        return getCoordinates(v).getY();
	}
	
    /**
     * @param v a Vertex of interest
     * @return the location point of the supplied vertex
     */
//	public Point3f getLocation(V v) {
//	    return getCoordinates(v);
//	}

	/**
	 * @param v
	 * @param xOffset
	 * @param yOffset
	 */
	protected void offsetVertex(V v, float xOffset, float yOffset, float zOffset) {
		Point3f c = getCoordinates(v);
        c.set(c.getX()+xOffset, c.getY()+yOffset, c.getZ()+zOffset);
		setLocation(v, c);
	}

	/**
	 * Accessor for the graph that represets all vertices.
	 * 
	 * @return the graph that contains all vertices.
	 */
	public Graph<V, E> getGraph() {
	    return graph;
	}
	
	/**
	 * Forcibly moves a vertex to the (x,y) location by setting its x and y
	 * locations to the inputted location. Does not add the vertex to the
	 * "dontmove" list, and (in the default implementation) does not make any
	 * adjustments to the rest of the graph.
	 */
	public void setLocation(V picked, float x, float y, float z) {
		Point3f coord = getCoordinates(picked);
		coord.set(x, y, z);
	}

	public void setLocation(V picked, Point3f p) {
		Point3f coord = getCoordinates(picked);
		coord.set(p);
	}

	/**
	 * Adds the vertex to the DontMove list
	 */
	public void lock(V v, boolean state) {
		if(state == true) dontmove.add(v);
		else dontmove.remove(v);
	}
	
	public void lock(boolean lock) {
		for(V v : graph.getVertices()) {
			lock(v, lock);
		}
	}
}
