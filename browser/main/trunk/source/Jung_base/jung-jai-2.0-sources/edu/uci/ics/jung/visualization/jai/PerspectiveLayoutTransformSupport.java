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

import javax.media.jai.PerspectiveTransform;

import edu.uci.ics.jung.algorithms.layout.GraphElementAccessor;
import edu.uci.ics.jung.visualization.Layer;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.picking.LayoutLensShapePickSupport;
/**
 * A class to make it easy to add a Perspective projection
 * to a jung graph application. See PerspectiveTransformerDemo
 * for an example of how to use it.
 * 
 * @author Tom Nelson
 *
 *
 */
public class PerspectiveLayoutTransformSupport<V,E> extends AbstractPerspectiveTransformSupport<V,E> 
    implements PerspectiveTransformSupport {

	protected GraphElementAccessor<V,E> pickSupport;
    /**
     * @param vv the VisualizationViewer to work on
     */
    public PerspectiveLayoutTransformSupport(VisualizationViewer<V,E> vv) {
        super(vv);
        this.perspectiveTransformer = 
            new PerspectiveShapeTransformer(new PerspectiveTransform(), 
            		vv.getRenderContext().getMultiLayerTransformer().getTransformer(Layer.LAYOUT));
        this.pickSupport = vv.getPickSupport();
   }
    
    public void activate() {
        lens = new Lens(perspectiveTransformer, vv.getSize());
        vv.getRenderContext().setPickSupport(new LayoutLensShapePickSupport<V,E>(vv));
        vv.getRenderContext().getMultiLayerTransformer().setTransformer(Layer.LAYOUT, perspectiveTransformer);
        vv.addPreRenderPaintable(lens);
        vv.setToolTipText(instructions);
        vv.repaint();
    }
    
    public void deactivate() {
        vv.getRenderContext().setPickSupport(pickSupport);
        if(perspectiveTransformer != null) {
            vv.removePreRenderPaintable(lens);
            vv.getRenderContext().getMultiLayerTransformer().setTransformer(Layer.LAYOUT, perspectiveTransformer.getDelegate());
        }
        vv.setToolTipText(defaultToolTipText);
        vv.repaint();
    }
}
