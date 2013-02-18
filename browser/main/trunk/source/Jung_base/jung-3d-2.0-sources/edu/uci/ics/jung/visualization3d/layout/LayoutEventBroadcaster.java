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

import javax.swing.event.ChangeListener;
import javax.vecmath.Point3f;

import edu.uci.ics.jung.algorithms.layout3d.Layout;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.visualization.util.ChangeEventSupport;
import edu.uci.ics.jung.visualization.util.DefaultChangeEventSupport;

/**
 * A LayoutDecorator the fires ChangeEvents when certain methods 
 * are called. Used to wrap a Layout so that the visualization
 * components can be notified of changes.
 * 
 * @see LayoutDecorator
 * @author Tom Nelson 
 *
 */
public class LayoutEventBroadcaster<V, E> extends LayoutDecorator<V,E> implements ChangeEventSupport {
    
    protected ChangeEventSupport changeSupport =
        new DefaultChangeEventSupport(this);

    public LayoutEventBroadcaster(Layout<V, E> delegate) {
    	super(delegate);
    }

    /**
     * @see edu.uci.ics.jung.algorithms.layout.Layout#step()
     */
    public void step() {
    	super.step();
    	fireStateChanged();
    }

    /**
	 * 
	 * @see edu.uci.ics.jung.algorithms.layout.Layout#initialize()
	 */
	public void initialize() {
		super.initialize();
		fireStateChanged();
	}

	/**
	 * @param v
	 * @param location
	 * @see edu.uci.ics.jung.algorithms.layout.Layout#setLocation(java.lang.Object, java.awt.geom.Point2D)
	 */
	public void setLocation(V v, Point3f location) {
		super.setLocation(v, location);
		fireStateChanged();
	}

    public void addChangeListener(ChangeListener l) {
        changeSupport.addChangeListener(l);
    }

    public void removeChangeListener(ChangeListener l) {
        changeSupport.removeChangeListener(l);
    }

    public ChangeListener[] getChangeListeners() {
        return changeSupport.getChangeListeners();
    }

    public void fireStateChanged() {
        changeSupport.fireStateChanged();
    }
    
    public void setGraph(Graph<V, E> graph) {
        delegate.setGraph(graph);
    }
}
