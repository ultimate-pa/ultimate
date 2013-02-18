/*
 * Copyright (c) 2005, the JUNG Project and the Regents of the University of
 * California All rights reserved.
 *
 * This software is open-source under the BSD license; see either "license.txt"
 * or http://jung.sourceforge.net/license.txt for a description.
 *
 * Created on Jul 11, 2005
 */

package edu.uci.ics.jung.visualization.jai;

import java.awt.Graphics2D;
import java.awt.Image;
import java.awt.Shape;
import java.awt.geom.AffineTransform;
import java.awt.geom.PathIterator;
import java.awt.geom.Point2D;
import java.awt.geom.Rectangle2D;
import java.awt.image.BufferedImage;
import java.awt.image.RenderedImage;
import java.awt.image.renderable.ParameterBlock;
import java.util.ArrayList;
import java.util.List;

import javax.media.jai.InterpolationNearest;
import javax.media.jai.JAI;
import javax.media.jai.PerspectiveTransform;
import javax.media.jai.WarpPerspective;
import javax.media.jai.operator.WarpDescriptor;
import javax.swing.Icon;

import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.visualization.Layer;
import edu.uci.ics.jung.visualization.RenderContext;
import edu.uci.ics.jung.visualization.renderers.BasicVertexRenderer;
import edu.uci.ics.jung.visualization.transform.shape.GraphicsDecorator;
import edu.uci.ics.jung.visualization.transform.shape.ShapeTransformer;
import edu.uci.ics.jung.visualization.transform.shape.TransformingGraphics;

/**
 * a subclass to apply a TransformingGraphics to certain operations
 * @author Tom Nelson
 *
 *
 */
public class TransformingImageVertexIconRenderer<V,E> extends BasicVertexRenderer<V,E> {
    
    WarpDescriptor warpDescriptor;
    
    /**
     * create an instance
     *
     */
    public TransformingImageVertexIconRenderer() {
        this.warpDescriptor = new WarpDescriptor();
    }
    
    @Override
    public void paintIconForVertex(RenderContext<V,E> rc, V v, Layout<V,E> layout) {

        GraphicsDecorator g = rc.getGraphicsContext();
        TransformingGraphics g2d = (TransformingGraphics)g;
        boolean vertexHit = true;
        // get the shape to be rendered
        Shape shape = rc.getVertexShapeTransformer().transform(v);
        
        Point2D p = layout.transform(v);
        p = rc.getMultiLayerTransformer().transform(Layer.LAYOUT, p);
        float x = (float)p.getX();
        float y = (float)p.getY();

        // create a transform that translates to the location of
        // the vertex to be rendered
        AffineTransform xform = AffineTransform.getTranslateInstance(x,y);
        // transform the vertex shape with xtransform
        shape = xform.createTransformedShape(shape);
        
        vertexHit = vertexHit(rc, shape);
        if (vertexHit) {
        	if(rc.getVertexIconTransformer() != null) {
        		Icon icon = rc.getVertexIconTransformer().transform(v);
        		if(icon != null) {
        		
                    BufferedImage image = new BufferedImage(icon.getIconWidth(), 
                            icon.getIconHeight(), BufferedImage.TYPE_INT_ARGB);
                    Graphics2D ig = image.createGraphics();
                    icon.paintIcon(null, ig, 0, 0);
                    int imageWidth = image.getWidth(null);
                    int imageHeight = image.getHeight(null);
                    
                    int xLoc = (int) (x - imageWidth / 2);
                    int yLoc = (int) (y - imageHeight / 2);
                    Rectangle2D imageRectangle = new Rectangle2D.Double(xLoc, yLoc,
                            imageWidth, imageHeight);
                    
                    Shape perspectiveShape = 
                        ((ShapeTransformer) g2d.getTransformer()).transform(imageRectangle);
                    
                    // see if the transformer will affect the imageRectangle,
                    if(imageRectangle.equals(perspectiveShape.getBounds2D()) == false) {
                        
                        RenderedImage ri = getPerspectiveImage(image, imageRectangle,
                                perspectiveShape);
                        
                        if (ri != null) {
                            
                            Shape clip = g2d.getClip();
                            g2d.setClip(perspectiveShape);
                            g2d.drawRenderedImage(ri, AffineTransform
                                    .getTranslateInstance(xLoc, yLoc));
                            g2d.setClip(clip);
                        }
                    } else {
                        g2d.drawImage(image, AffineTransform.getTranslateInstance(xLoc,
                                yLoc), null);
                    }

        		} else {
        			paintShapeForVertex(rc, v, shape);
        		}
        	} else {
        		paintShapeForVertex(rc, v, shape);
        	}
        }
    }
    
    protected RenderedImage getPerspectiveImage(Image image, Shape imageShape, Shape perspectiveShape) {
        
        Rectangle2D imageRectangle = imageShape.getBounds2D();
        double imagex1 = imageRectangle.getX();
        double imagey1 = imageRectangle.getY();
        double imagex2 = imageRectangle.getMaxX();
        double imagey2 = imageRectangle.getMaxY();
        
        double width = imagex2 - imagex1;
        double height = imagey2 - imagey1;
        
        double quadx1 = 0;
        double quady1 = 0;
        double quadx2 = 0;
        double quady2 = 0;
        double quadx3 = 0;
        double quady3 = 0;
        double quadx4 = 0;
        double quady4 = 0;
        
        List<Point2D> quadList = new ArrayList<Point2D>();
        
        for(PathIterator iterator=perspectiveShape.getPathIterator(null);
            iterator.isDone() == false; iterator.next()) {
            
            float[] coords = new float[6];
            int type = iterator.currentSegment(coords);
            switch(type) {
            case PathIterator.SEG_MOVETO:
                quadList.add(new Point2D.Float(coords[0], coords[1]));
                break;
            case PathIterator.SEG_LINETO:
                quadList.add(new Point2D.Float(coords[0], coords[1]));
                break;
            }
        }
        Point2D pt1 = quadList.remove(0);
        Point2D pt2 = quadList.remove(0);
        Point2D pt3 = quadList.remove(0);
        Point2D pt4 = quadList.remove(0);
        
        quadx1 = pt1.getX()-imagex1;
        quady1 = pt1.getY()-imagey1;
        
        quadx2 = pt2.getX()-imagex1;
        quady2 = pt2.getY()-imagey1;
        
        quadx3 = pt3.getX()-imagex1;
        quady3 = pt3.getY()-imagey1;
        
        quadx4 = pt4.getX()-imagex1;
        quady4 = pt4.getY()-imagey1;
        
        RenderedImage srcImage = null;
        if(image instanceof RenderedImage) {
            srcImage = (RenderedImage)image;
        } else {
            srcImage = getBufferedImage(image);
        }
        
        PerspectiveTransform perspectiveTransform =
            PerspectiveTransform.getQuadToQuad(
                    
                    quadx1, quady1,
                    quadx2, quady2,
                    quadx3, quady3,
                    quadx4, quady4,
                    
                    0, 0,
                    width, 0,
                    width, height,
                    0, height
                    );
        
        double[][] matrix = new double[3][3];
        perspectiveTransform.getMatrix(matrix);
        
        if(matrix[2][2] == 0 || Double.isNaN(matrix[2][2])) {
            System.err.println("matrix[2][2] = "+matrix[2][2]);
            return null;
        }
        if(matrix[1][1] == 0 || Double.isNaN(matrix[1][1])) {
            System.err.println("matrix[1][1] = "+matrix[1][1]);
            return null;
        }
        if(matrix[0][0] == 0 || Double.isNaN(matrix[0][0])) {
            System.err.println("matrix[0][0] = "+matrix[0][0]);
           return null;
        }
        
        WarpPerspective warp = new WarpPerspective(perspectiveTransform);
        ParameterBlock pm = new ParameterBlock();
        pm.addSource(srcImage);
        pm.add(warp);
        pm.add(new InterpolationNearest());
        
        RenderedImage dstImage = JAI.create("warp", pm);
        
        return dstImage;
        
    }
    
    private BufferedImage getBufferedImage(Image image) {
        int width = image.getWidth(null);
        int height = image.getHeight(null);
        BufferedImage bi = new BufferedImage(width, height, BufferedImage.TYPE_INT_ARGB);
        Graphics2D g = bi.createGraphics();
        g.drawImage(image, 0, 0, null);
        g.dispose();
        return bi;
    }
}
