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
import edu.uci.ics.jung.visualization.RenderContext;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.picking.ViewLensShapePickSupport;
import edu.uci.ics.jung.visualization.renderers.BasicRenderer;
import edu.uci.ics.jung.visualization.renderers.Renderer;
import edu.uci.ics.jung.visualization.transform.shape.GraphicsDecorator;
import edu.uci.ics.jung.visualization.transform.shape.TransformingGraphics;
/**
 * A class to make it easy to add a Perspective projection
 * to a jung graph application. See PerspectiveTransformerDemo
 * for an example of how to use it.
 * 
 * @author Tom Nelson
 */
public class PerspectiveImageLensSupport<V,E> extends AbstractPerspectiveTransformSupport<V,E> {
    
    protected RenderContext<V,E> renderContext;
    protected GraphicsDecorator lensGraphicsDecorator;
    protected GraphicsDecorator savedGraphicsDecorator;
    protected Renderer<V,E> renderer;
    protected Renderer<V,E> transformingRenderer;
	protected GraphElementAccessor<V,E> pickSupport;
    
    static final String instructions = "";
    
    /**
     * @param vv the VisualizationViewer to work on
     */
    public PerspectiveImageLensSupport(VisualizationViewer<V,E> vv) {
        super(vv);
        this.renderContext = vv.getRenderContext();
        this.pickSupport = renderContext.getPickSupport();
        this.renderer = vv.getRenderer();
        this.transformingRenderer = new BasicRenderer<V,E>();
        this.perspectiveTransformer = 
            new PerspectiveShapeTransformer(new PerspectiveTransform(), vv.getRenderContext().getMultiLayerTransformer().getTransformer(Layer.VIEW));
        this.transformingRenderer.setVertexRenderer(new TransformingImageVertexIconRenderer<V,E>());
        this.lensGraphicsDecorator = new TransformingGraphics(perspectiveTransformer);
        this.savedGraphicsDecorator = renderContext.getGraphicsContext();

        this.renderer = vv.getRenderer();
    }
    
    public void activate() {
        lens = new Lens(perspectiveTransformer, vv.getSize());
        renderContext.setPickSupport(new ViewLensShapePickSupport<V,E>(vv));
        vv.getRenderContext().getMultiLayerTransformer().setTransformer(Layer.VIEW, perspectiveTransformer);
        vv.getRenderContext().setGraphicsContext(lensGraphicsDecorator);
        vv.setRenderer(transformingRenderer);
        vv.addPreRenderPaintable(lens);
        vv.setToolTipText(instructions);
        vv.repaint();
    }
    
    public void deactivate() {
    	renderContext.setPickSupport(pickSupport);
        vv.getRenderContext().getMultiLayerTransformer().setTransformer(Layer.VIEW, perspectiveTransformer.getDelegate());
        vv.removePreRenderPaintable(lens);
        vv.getRenderContext().setGraphicsContext(savedGraphicsDecorator);
        vv.setRenderer(renderer);
        vv.setToolTipText(defaultToolTipText);
        vv.repaint();
    }
}
