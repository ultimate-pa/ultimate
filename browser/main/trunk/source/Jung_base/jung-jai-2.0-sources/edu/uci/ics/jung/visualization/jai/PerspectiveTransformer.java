/*
 * Copyright (c) 2003, the JUNG Project and the Regents of the University of
 * California All rights reserved.
 * 
 * This software is open-source under the BSD license; see either "license.txt"
 * or http://jung.sourceforge.net/license.txt for a description.
 * 
 */
package edu.uci.ics.jung.visualization.jai;

import java.awt.geom.NoninvertibleTransformException;
import java.awt.geom.Point2D;

import javax.media.jai.PerspectiveTransform;

import edu.uci.ics.jung.visualization.transform.MutableAffineTransformer;
import edu.uci.ics.jung.visualization.transform.MutableTransformer;
import edu.uci.ics.jung.visualization.transform.MutableTransformerDecorator;

/**
 * PerspectiveTransformer wraps a MutableAffineTransformer and modifies
 * the transform and inverseTransform methods so that they create a
 * perspective projection of the graph points.
 * 
 * @author Tom Nelson
 *
 */
public class PerspectiveTransformer extends MutableTransformerDecorator implements MutableTransformer {

    protected PerspectiveTransform perspectiveTransform;
    /**
     * create an instance, setting values from the passed component
     * and registering to listen for size changes on the component
     * @param component
     */
    public PerspectiveTransformer(PerspectiveTransform perspectiveTransform) {
        this(perspectiveTransform, new MutableAffineTransformer());
    }
    /**
     * create an instance with a possibly shared transform
     * @param component
     * @param delegate
     */
    public PerspectiveTransformer(PerspectiveTransform perspectiveTransform, MutableTransformer delegate) {
    		super(delegate);
    		this.perspectiveTransform = perspectiveTransform;
   }
    
    @Override
    public void setToIdentity() {
        this.perspectiveTransform.setToIdentity();
    }
    
    public PerspectiveTransform createInverse() {
        try {
            return perspectiveTransform.createInverse();
        } catch (NoninvertibleTransformException e) {
            e.printStackTrace();
        } catch (CloneNotSupportedException e) {
            e.printStackTrace();
        }
        return null;
    }

    /**
     * override base class transform to project the perspective effect
     */
    @Override
    public Point2D transform(Point2D graphPoint) {
        if(graphPoint == null) return null;
        Point2D p2 = super.transform(graphPoint);
        return perspectiveTransform.transform(p2, null);
    }
    
    /**
     * override base class to un-project the perspective effect
     */
    @Override
    public Point2D inverseTransform(Point2D viewPoint) {
        Point2D p2 = createInverse().transform(viewPoint, null);
        return super.inverseTransform(p2);

    }
    public Point2D perspectiveTransform(Point2D graphPoint) {
        if(graphPoint == null) return null;
        return perspectiveTransform.transform(graphPoint, null);
    }
    
    /**
     * override base class to un-project the perspective effect
     */
    public Point2D inversePerspectiveTransform(Point2D viewPoint) {
        return createInverse().transform(viewPoint, null);
    }

    public PerspectiveTransform getPerspectiveTransform() {
        return perspectiveTransform;
    }
    public void setPerspectiveTransform(PerspectiveTransform perspectiveTransform) {
        this.perspectiveTransform = perspectiveTransform;
    }
}