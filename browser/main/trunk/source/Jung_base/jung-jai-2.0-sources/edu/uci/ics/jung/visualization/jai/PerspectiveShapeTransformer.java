/*
 * Copyright (c) 2003, the JUNG Project and the Regents of the University of
 * California All rights reserved.
 * 
 * This software is open-source under the BSD license; see either "license.txt"
 * or http://jung.sourceforge.net/license.txt for a description.
 * 
 */
package edu.uci.ics.jung.visualization.jai;

import java.awt.Shape;
import java.awt.geom.GeneralPath;
import java.awt.geom.PathIterator;
import java.awt.geom.Point2D;

import javax.media.jai.PerspectiveTransform;

import edu.uci.ics.jung.visualization.transform.MutableTransformer;
import edu.uci.ics.jung.visualization.transform.shape.ShapeTransformer;

/**
 * PerspectiveShapeTransformer extends PerspectiveTransformer and
 * adds implementations for methods in ShapeTransformer.
 * It modifies the shapes (Vertex, Edge, and Arrowheads) so that
 * they are distorted by the perspective transformation
 * 
 * @author Tom Nelson
 *
 *
 */
public class PerspectiveShapeTransformer extends PerspectiveTransformer 
    implements ShapeTransformer {

    /**
     * Create an instance, setting values from the passed component
     * and registering to listen for size changes on the component.
     */
    public PerspectiveShapeTransformer(PerspectiveTransform perspectiveTransform) {
        this(perspectiveTransform, null);
    }
    
    /**
     * Create an instance
     */
    public PerspectiveShapeTransformer(PerspectiveTransform perspectiveTransform, MutableTransformer delegate) {
        super(perspectiveTransform, delegate);
   }
    
    /**
     * Transform the supplied shape with the overridden transform
     * method so that the shape is distorted by the perspective 
     * transform.
     * @param shape a shape to transform
     * @return a GeneralPath for the transformed shape
     */
    @Override
    public Shape transform(Shape shape) {
        return transform(shape, 0);
    }
    public Shape transform(Shape shape, float flatness) {
        GeneralPath newPath = new GeneralPath();
        float[] coords = new float[6];
        PathIterator iterator = null;
        if(flatness == 0) {
            iterator = shape.getPathIterator(null);
        } else {
            iterator = shape.getPathIterator(null, flatness);
        }
        for( ;
            iterator.isDone() == false;
            iterator.next()) {
            int type = iterator.currentSegment(coords);
            switch(type) {
            case PathIterator.SEG_MOVETO:
                Point2D p = transform(new Point2D.Float(coords[0], coords[1]));
                newPath.moveTo((float)p.getX(), (float)p.getY());
                break;
                
            case PathIterator.SEG_LINETO:
                p = transform(new Point2D.Float(coords[0], coords[1]));
                newPath.lineTo((float)p.getX(), (float) p.getY());
                break;
                
            case PathIterator.SEG_QUADTO:
                p = transform(new Point2D.Float(coords[0], coords[1]));
                Point2D q = transform(new Point2D.Float(coords[2], coords[3]));
                newPath.quadTo((float)p.getX(), (float)p.getY(), (float)q.getX(), (float)q.getY());
                break;
                
            case PathIterator.SEG_CUBICTO:
                p = transform(new Point2D.Float(coords[0], coords[1]));
                q = transform(new Point2D.Float(coords[2], coords[3]));
                Point2D r = transform(new Point2D.Float(coords[4], coords[5]));
                newPath.curveTo((float)p.getX(), (float)p.getY(), 
                        (float)q.getX(), (float)q.getY(),
                        (float)r.getX(), (float)r.getY());
                break;
                
            case PathIterator.SEG_CLOSE:
                newPath.closePath();
                break;
                    
            }
        }
        return newPath;
    }
    
    @Override
    public Shape inverseTransform(Shape shape) {
        GeneralPath newPath = new GeneralPath();
        float[] coords = new float[6];
        for(PathIterator iterator=shape.getPathIterator(null);
            iterator.isDone() == false;
            iterator.next()) {
            int type = iterator.currentSegment(coords);
            switch(type) {
            case PathIterator.SEG_MOVETO:
                Point2D p = inverseTransform(new Point2D.Float(coords[0], coords[1]));
                newPath.moveTo((float)p.getX(), (float)p.getY());
                break;
                
            case PathIterator.SEG_LINETO:
                p = inverseTransform(new Point2D.Float(coords[0], coords[1]));
                newPath.lineTo((float)p.getX(), (float) p.getY());
                break;
                
            case PathIterator.SEG_QUADTO:
                p = inverseTransform(new Point2D.Float(coords[0], coords[1]));
                Point2D q = inverseTransform(new Point2D.Float(coords[2], coords[3]));
                newPath.quadTo((float)p.getX(), (float)p.getY(), (float)q.getX(), (float)q.getY());
                break;
                
            case PathIterator.SEG_CUBICTO:
                p = inverseTransform(new Point2D.Float(coords[0], coords[1]));
                q = inverseTransform(new Point2D.Float(coords[2], coords[3]));
                Point2D r = inverseTransform(new Point2D.Float(coords[4], coords[5]));
                newPath.curveTo((float)p.getX(), (float)p.getY(), 
                        (float)q.getX(), (float)q.getY(),
                        (float)r.getX(), (float)r.getY());
                break;
                
            case PathIterator.SEG_CLOSE:
                newPath.closePath();
                break;
                    
            }
        }
        return newPath;
    }
    
    public Shape perspectiveTransform(Shape shape) {
        return perspectiveTransform(shape, 0);
    }

    public Shape perspectiveTransform(Shape shape, float flatness) {
        GeneralPath newPath = new GeneralPath();
        float[] coords = new float[6];
        PathIterator iterator = null;
        if(flatness == 0) {
            iterator = shape.getPathIterator(null);
        } else {
            iterator = shape.getPathIterator(null, flatness);
        }
        for( ;
            iterator.isDone() == false;
            iterator.next()) {
            int type = iterator.currentSegment(coords);
            switch(type) {
            case PathIterator.SEG_MOVETO:
                Point2D p = perspectiveTransform(new Point2D.Float(coords[0], coords[1]));
                newPath.moveTo((float)p.getX(), (float)p.getY());
                break;
                
            case PathIterator.SEG_LINETO:
                p = perspectiveTransform(new Point2D.Float(coords[0], coords[1]));
                newPath.lineTo((float)p.getX(), (float) p.getY());
                break;
                
            case PathIterator.SEG_QUADTO:
                p = perspectiveTransform(new Point2D.Float(coords[0], coords[1]));
                Point2D q = perspectiveTransform(new Point2D.Float(coords[2], coords[3]));
                newPath.quadTo((float)p.getX(), (float)p.getY(), (float)q.getX(), (float)q.getY());
                break;
                
            case PathIterator.SEG_CUBICTO:
                p = perspectiveTransform(new Point2D.Float(coords[0], coords[1]));
                q = perspectiveTransform(new Point2D.Float(coords[2], coords[3]));
                Point2D r = perspectiveTransform(new Point2D.Float(coords[4], coords[5]));
                newPath.curveTo((float)p.getX(), (float)p.getY(), 
                        (float)q.getX(), (float)q.getY(),
                        (float)r.getX(), (float)r.getY());
                break;
                
            case PathIterator.SEG_CLOSE:
                newPath.closePath();
                break;
                    
            }
        }
        return newPath;
    }

    public Shape inversePerspectiveTransform(Shape shape) {
        GeneralPath newPath = new GeneralPath();
        float[] coords = new float[6];
        for(PathIterator iterator=shape.getPathIterator(null);
            iterator.isDone() == false;
            iterator.next()) {
            int type = iterator.currentSegment(coords);
            switch(type) {
            case PathIterator.SEG_MOVETO:
                Point2D p = inversePerspectiveTransform(new Point2D.Float(coords[0], coords[1]));
                newPath.moveTo((float)p.getX(), (float)p.getY());
                break;
                
            case PathIterator.SEG_LINETO:
                p = inversePerspectiveTransform(new Point2D.Float(coords[0], coords[1]));
                newPath.lineTo((float)p.getX(), (float) p.getY());
                break;
                
            case PathIterator.SEG_QUADTO:
                p = inversePerspectiveTransform(new Point2D.Float(coords[0], coords[1]));
                Point2D q = inversePerspectiveTransform(new Point2D.Float(coords[2], coords[3]));
                newPath.quadTo((float)p.getX(), (float)p.getY(), (float)q.getX(), (float)q.getY());
                break;
                
            case PathIterator.SEG_CUBICTO:
                p = inversePerspectiveTransform(new Point2D.Float(coords[0], coords[1]));
                q = inversePerspectiveTransform(new Point2D.Float(coords[2], coords[3]));
                Point2D r = inversePerspectiveTransform(new Point2D.Float(coords[4], coords[5]));
                newPath.curveTo((float)p.getX(), (float)p.getY(), 
                        (float)q.getX(), (float)q.getY(),
                        (float)r.getX(), (float)r.getY());
                break;
                
            case PathIterator.SEG_CLOSE:
                newPath.closePath();
                break;
                    
            }
        }
        return newPath;
    }

}