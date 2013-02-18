/*
 * Copyright (c) 2003, the JUNG Project and the Regents of the University of
 * California All rights reserved.
 * 
 * This software is open-source under the BSD license; see either "license.txt"
 * or http://jung.sourceforge.net/license.txt for a description.
 * 
 */
package edu.uci.ics.jung.visualization.jai;

import javax.media.jai.PerspectiveTransform;

import edu.uci.ics.jung.algorithms.layout.GraphElementAccessor;
import edu.uci.ics.jung.visualization.Layer;
import edu.uci.ics.jung.visualization.RenderContext;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.picking.ViewLensShapePickSupport;
import edu.uci.ics.jung.visualization.renderers.Renderer;
import edu.uci.ics.jung.visualization.transform.shape.GraphicsDecorator;
import edu.uci.ics.jung.visualization.transform.shape.TransformingGraphics;

/**
 * Creates a PerspectiveShapeTransformer to use in the view
 * transform. This one will distort Vertex shapes.
 * 
 * @author Tom Nelson
 *
 *
 */
public class PerspectiveViewTransformSupport<V,E> extends AbstractPerspectiveTransformSupport<V,E>
    implements PerspectiveTransformSupport {
    
	protected RenderContext<V,E> renderContext;
    protected Renderer<V,E> renderer;
    protected GraphicsDecorator lensGraphicsDecorator;
    protected GraphicsDecorator savedGraphicsDecorator;
    protected GraphElementAccessor<V,E> pickSupport;

    public PerspectiveViewTransformSupport(VisualizationViewer<V,E> vv) {
        super(vv);
        this.renderer = vv.getRenderer();
        this.renderContext = vv.getRenderContext();
        this.pickSupport = renderContext.getPickSupport();
        this.perspectiveTransformer = 
            new PerspectiveShapeTransformer(new PerspectiveTransform(), 
            		vv.getRenderContext().getMultiLayerTransformer().getTransformer(Layer.VIEW));
        this.savedGraphicsDecorator = renderContext.getGraphicsContext();
        this.lensGraphicsDecorator = new TransformingGraphics(perspectiveTransformer);
    }
    
    public void activate() {
        lens = new Lens(perspectiveTransformer, vv.getSize());
        renderContext.setPickSupport(new ViewLensShapePickSupport<V,E>(vv));
        vv.getRenderContext().getMultiLayerTransformer().setTransformer(Layer.VIEW, perspectiveTransformer);
        vv.getRenderContext().setGraphicsContext(lensGraphicsDecorator);
        vv.addPreRenderPaintable(lens);
        vv.setToolTipText(instructions);
        vv.repaint();
    }

    public void deactivate() {
    	renderContext.setPickSupport(pickSupport);
        vv.getRenderContext().getMultiLayerTransformer().setTransformer(Layer.VIEW, perspectiveTransformer.getDelegate());
        vv.removePreRenderPaintable(lens);
        vv.getRenderContext().setGraphicsContext(savedGraphicsDecorator);
        vv.setToolTipText(defaultToolTipText);
        vv.repaint();
    }

}