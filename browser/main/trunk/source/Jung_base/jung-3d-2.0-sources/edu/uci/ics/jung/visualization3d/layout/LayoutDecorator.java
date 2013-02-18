/*
 * Copyright (c) 2005, the JUNG Project and the Regents of the University of
 * California All rights reserved.
 *
 * This software is open-source under the BSD license; see either "license.txt"
 * or http://jung.sourceforge.net/license.txt for a description.
 *
 * Created on Aug 23, 2005
 */

package edu.uci.ics.jung.visualization3d.layout;

import javax.media.j3d.BoundingSphere;
import javax.vecmath.Point3f;

import org.apache.commons.collections15.Transformer;

import edu.uci.ics.jung.algorithms.layout3d.Layout;
import edu.uci.ics.jung.algorithms.util.IterativeContext;
import edu.uci.ics.jung.graph.Graph;

/**
 * a pure decorator for the Layout interface. Intended to be overridden
 * to provide specific behavior decoration
 * 
 * @author Tom Nelson 
 *
 */
public abstract class LayoutDecorator<V, E> implements Layout<V, E>, IterativeContext {
    
    protected Layout<V, E> delegate;
    
    public LayoutDecorator(Layout<V, E> delegate) {
        this.delegate = delegate;
    }

    /**
     * getter for the delegate
     * @return the delegate
     */
    public Layout getDelegate() {
        return delegate;
    }

    /**
     * setter for the delegate
     * @param delegate the new delegate
     */
    public void setDelegate(Layout<V,E> delegate) {
        this.delegate = delegate;
    }

    /**
     * @see edu.uci.ics.jung.algorithms.layout.Layout#step()
     */
    public void step() {
    	if(delegate instanceof IterativeContext) {
    		((IterativeContext)delegate).step();
    	}
    }

    /**
	 * 
	 * @see edu.uci.ics.jung.algorithms.layout.Layout#initialize()
	 */
	public void initialize() {
		delegate.initialize();
	}

	/**
	 * @param initializer
	 * @see edu.uci.ics.jung.algorithms.layout.Layout#setInitializer(org.apache.commons.collections15.Transformer)
	 */
	public void setInitializer(Transformer<V, Point3f> initializer) {
		delegate.setInitializer(initializer);
	}

	/**
	 * @param v
	 * @param location
	 * @see edu.uci.ics.jung.algorithms.layout.Layout#setLocation(java.lang.Object, java.awt.geom.Point3f)
	 */
	public void setLocation(V v, Point3f location) {
		delegate.setLocation(v, location);
	}

    /**
     * @see edu.uci.ics.jung.algorithms.layout.Layout#getCurrentSize()
     */
    public BoundingSphere getSize() {
        return delegate.getSize();
    }

    /**
     * @see edu.uci.ics.jung.algorithms.layout.Layout#getGraph()
     */
    public Graph<V, E> getGraph() {
        return delegate.getGraph();
    }

    /**
     * @see edu.uci.ics.jung.algorithms.layout.Layout#getLocation(edu.uci.ics.jung.graph.ArchetypeVertex)
     */
    public Point3f transform(V v) {
        return delegate.transform(v);
    }

    /**
     * @see edu.uci.ics.jung.algorithms.layout.Layout#done()
     */
    public boolean done() {
    	if(delegate instanceof IterativeContext) {
    		return ((IterativeContext)delegate).done();
    	}
    	return true;
    }

    /**
     * @see edu.uci.ics.jung.algorithms.layout.Layout#lockVertex(edu.uci.ics.jung.graph.Vertex)
     */
    public void lock(V v, boolean state) {
        delegate.lock(v, state);
    }

    /**
     * @see edu.uci.ics.jung.algorithms.layout.Layout#isLocked(V)
     */
    public boolean isLocked(V v) {
        return delegate.isLocked(v);
    }
    
    /**
     * @see edu.uci.ics.jung.algorithms.layout.Layout#resize(java.awt.Dimension)
     */
    public void setSize(BoundingSphere d) {
        delegate.setSize(d);
    }

    /**
     * @see edu.uci.ics.jung.algorithms.layout.Layout#reset()
     */
    public void reset() {
    	delegate.reset();
    }
    
    public void setGraph(Graph<V, E> graph) {
        delegate.setGraph(graph);
    }
}
