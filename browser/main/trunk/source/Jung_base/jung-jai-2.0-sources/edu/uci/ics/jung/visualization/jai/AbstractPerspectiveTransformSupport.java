/*
 * Copyright (c) 2005, the JUNG Project and the Regents of the University of
 * California All rights reserved.
 *
 * This software is open-source under the BSD license; see either "license.txt"
 * or http://jung.sourceforge.net/license.txt for a description.
 *
 * Created on Jul 21, 2005
 */

package edu.uci.ics.jung.visualization.jai;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Shape;
import java.awt.geom.Rectangle2D;

import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.VisualizationServer.Paintable;


/**
 * A class to make it easy to add a perspective projection
 * examining lens to a jung graph application. See PerspectiveTransformerDemo
 * for an example of how to use it.
 * 
 * @author Tom Nelson
 *
 *
 */
public abstract class AbstractPerspectiveTransformSupport<V,E> implements PerspectiveTransformSupport {

    protected VisualizationViewer<V,E> vv;
    protected PerspectiveShapeTransformer perspectiveTransformer;
    protected Lens lens;
    protected String defaultToolTipText;

    protected static final String instructions = 
        "<html><center>The mouse mode button is<p>"+
        "in the lower-right corner<p>"+
        "of the scroll-pane.</center></html>";
    
    /**
     * create the base class, setting common members and creating
     * a custom GraphMouse
     * @param vv the VisualizationViewer to work on
     */
    public AbstractPerspectiveTransformSupport(VisualizationViewer<V,E> vv) {
        this.vv = vv;
        this.defaultToolTipText = vv.getToolTipText();
    }

    public void activate(boolean state) {
        if(state) activate();
        else deactivate();
    }
    
    public PerspectiveShapeTransformer getPerspectiveTransformer() {
        return perspectiveTransformer;
    }

    public void setPerspectiveTransformer(
            PerspectiveShapeTransformer perspectiveTransformer) {
        this.perspectiveTransformer = perspectiveTransformer;
    }

    /**
     * the background for the perspective projection
     * @author Tom Nelson 
     *
     *
     */
    public static class Lens implements Paintable {
        PerspectiveShapeTransformer perspectiveTransformer;
        Rectangle2D rectangle;
        
        public Lens(PerspectiveShapeTransformer perspectiveTransformer, Dimension d) {
            this.perspectiveTransformer = perspectiveTransformer;
            this.rectangle = 
            	new Rectangle2D.Float(d.width/8,d.height/8,
            			3*d.width/4,3*d.height/4);
        }
        
        /**
         * @return Returns the hyperbolicTransformer.
         */

        public void paint(Graphics g) {
            
            Graphics2D g2d = (Graphics2D)g;
            g.setColor(Color.decode("0xdddddd"));
            Shape shape = perspectiveTransformer.perspectiveTransform(rectangle);
            g2d.fill(shape);
            g.setColor(Color.gray);
            g2d.draw(shape);
        }

        public boolean useTransform() {
            return true;
        }
    }
}
