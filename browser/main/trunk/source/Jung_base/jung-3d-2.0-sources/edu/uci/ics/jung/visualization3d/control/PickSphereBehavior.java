/*
 * Copyright (c) 2003, the JUNG Project and the Regents of the University of
 * California All rights reserved.
 * 
 * This software is open-source under the BSD license; see either "license.txt"
 * or http://jung.sourceforge.net/license.txt for a description.
 */
package edu.uci.ics.jung.visualization3d.control;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;

import javax.media.j3d.Bounds;
import javax.media.j3d.BranchGroup;
import javax.media.j3d.Canvas3D;
import javax.media.j3d.Node;
import javax.media.j3d.Transform3D;
import javax.media.j3d.TransformGroup;
import javax.vecmath.Point3d;
import javax.vecmath.Vector3d;

import com.sun.j3d.utils.geometry.Primitive;
import com.sun.j3d.utils.picking.PickResult;
import com.sun.j3d.utils.picking.PickTool;

/**
 * A mouse behavior that allows user to pick and translate scene 
 * graph objects.
 * Common usage: 
 *   1. Create your scene graph. 
 *   2. Create this behavior with the root and canvas. 
 * See PickRotateBehavior for more details.
 */

public class PickSphereBehavior extends PickTranslateBehavior {
    
    Node oldShape;
    PropertyChangeSupport support;
    TransformGroup currGrp;
    double x_factor = .005;
    double y_factor = .005;
    double dx, dy;
    Vector3d translation = new Vector3d();
    Canvas3D canvas;
    
    public PickSphereBehavior(BranchGroup root, Canvas3D canvas, 
            Bounds bounds){
        super(root, canvas, bounds);
        setCanvas(canvas);
        this.setSchedulingBounds(bounds);
        root.addChild(this);
        pickCanvas.setMode(PickTool.GEOMETRY);
        pickCanvas.setTolerance(0.f);
    }
    
    public void setTransformGroup(TransformGroup t) {
        currGrp = t;
    }
    
    public void setCanvas(Canvas3D canvas) {
        this.canvas = canvas;
    }
    
    public void updateScene(int xpos, int ypos) {
    	System.err.println("update scene ");
        PickResult pickResult = null;
        Primitive shape = null;

        pickCanvas.setShapeLocation(xpos, ypos);
        pickResult = pickCanvas.pickClosest();
        
        if (pickResult != null) {
            
            shape = (Primitive) pickResult.getNode(PickResult.PRIMITIVE);
            if(shape != null) {
                
                firePropertyChange("PeakSelected",
                        oldShape,
                        shape);
                oldShape = shape;
                setTransformGroup((TransformGroup)shape.getParent());
                changeTranslation(xpos,ypos);
            }
        }
    }   
    
    private void changeTranslation(int x, int y) {
        Transform3D currXform = new Transform3D();
        Transform3D transformX = new Transform3D();
        Transform3D transformY = new Transform3D();
        
        // fill currXform with the current values
        currGrp.getTransform(currXform);
        
        Point3d position = new Point3d();
        canvas.getPixelLocationInImagePlate(x, y, position);
        
        Transform3D imagePlateToVworldTransform = new Transform3D();
        canvas.getImagePlateToVworld(imagePlateToVworldTransform);
        
        translation.x = position.x;
        translation.y = position.y;
        
        transformX.set(translation);
        
        transformY.mul(imagePlateToVworldTransform, transformX);
        
        // now i just want the translational part of transformY
        Vector3d trans = new Vector3d();
        transformY.get(trans);
        
        trans.x = -trans.x;
        trans.y = -trans.y;
        
        transformX.set(trans);
        
        currXform.mul(transformX, currXform);
        
        currGrp.setTransform(currXform);
    }
    
    public void addPropertyChangeListener(PropertyChangeListener l) {
        if(support == null) {
            support = new PropertyChangeSupport(this);
        }
        support.addPropertyChangeListener(l);
    }
    
    public void removePropertyChangeListener(PropertyChangeListener l) {
        if(support != null) {
            support.removePropertyChangeListener(l);
        }
    }
    
    public void firePropertyChange(String name, Object oldValue, Object newValue) {
        if(support != null) {
            support.firePropertyChange(name, oldValue, newValue);
        }
    }
}
