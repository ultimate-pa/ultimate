/*
 * Copyright (c) 2003, the JUNG Project and the Regents of the University of
 * California All rights reserved.
 * 
 * This software is open-source under the BSD license; see either "license.txt"
 * or http://jung.sourceforge.net/license.txt for a description.
 */
package edu.uci.ics.jung.visualization3d;

import javax.media.j3d.Appearance;
import javax.media.j3d.LineArray;
import javax.media.j3d.Material;
import javax.media.j3d.Node;
import javax.media.j3d.Shape3D;
import javax.vecmath.Color3f;
import javax.vecmath.Point3f;

import org.apache.commons.collections15.Transformer;
import org.apache.commons.collections15.functors.ConstantTransformer;

import com.sun.j3d.utils.geometry.Box;
import com.sun.j3d.utils.geometry.Cylinder;
import com.sun.j3d.utils.geometry.Sphere;

import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.util.Context;
import edu.uci.ics.jung.visualization.picking.PickedState;


/**
 */
@SuppressWarnings("unchecked")
public class PluggableRenderContext<V, E> implements RenderContext<V, E> {

	protected Transformer<E,Appearance> edgeAppearanceTransformer;
	protected Transformer<Context<Graph<V,E>,E>,Node> edgeShapeTransformer;
	protected PickedState<E> pickedEdgeState;
	protected PickedState<V> pickedVertexState;
	protected Transformer<V,Appearance> vertexAppearanceTransformer;
	protected Transformer<V,String> vertexStringer = new ConstantTransformer(null);
	protected Transformer<V,Node> vertexShapeTransformer;
	
	
	
	public PluggableRenderContext() {
		super();
		Color3f lightGray = new Color3f(0.7f, 0.7f, 0.7f);
		Color3f black = new Color3f(0,0,0);
		Color3f white = new Color3f(1,1,1);
		Color3f gray  = new Color3f(.2f, .2f, .2f);
		Color3f red = new Color3f(1, 0, 0);
		Color3f yellow = new Color3f(0,1,1);
		Material lightGrayMaterial = new Material(lightGray, black,
				lightGray, white, 100.0f);
		Material blackMaterial = new Material(lightGray, black,
				black, lightGray, 10.0f);
		Material whiteMaterial = new Material(white, white,
				white, white, 100.0f);
		Material grayMaterial = new Material(gray, black,
				gray, gray, 100.0f);
		Material redMaterial = new Material(red, black,
				red, red, 100.0f);
		Material yellowMaterial = new Material(yellow, black,
				yellow, yellow, 100.0f);

		final Appearance lightGrayLook = new Appearance();
		lightGrayLook.setMaterial(lightGrayMaterial);
		Appearance blackLook = new Appearance();
		blackLook.setMaterial(blackMaterial);
		Appearance whiteLook = new Appearance();
		whiteLook.setMaterial(whiteMaterial);
		Appearance grayLook = new Appearance();
		grayLook.setMaterial(grayMaterial);
		
//		grayLook.setCapability(Appearance.ALLOW_MATERIAL_READ);
//		grayLook.setCapability(Appearance.ALLOW_MATERIAL_WRITE);

		final Appearance redLook = new Appearance();
		redLook.setMaterial(redMaterial);
		final Appearance yellowLook = new Appearance();
		yellowLook.setMaterial(yellowMaterial);
		
		 final Cylinder cylinder = new Cylinder(1, 1, 
				 Cylinder.GENERATE_NORMALS |
				 Cylinder.ENABLE_GEOMETRY_PICKING,
				 26, 26, lightGrayLook);
	      final Sphere sphere = new Sphere(10, 
	    		  Sphere.GENERATE_NORMALS | 
	    		  Sphere.ENABLE_GEOMETRY_PICKING, redLook);
	      final Box box = new Box(10,10,10,
	    		  Box.GENERATE_NORMALS |
	    		  Box.ENABLE_GEOMETRY_PICKING,
	    		  redLook);

		this.edgeAppearanceTransformer = new ConstantTransformer(lightGrayLook);
		this.edgeShapeTransformer = new Transformer<Context<Graph<V,E>,E>,Node>() {

			public Node transform(Context<Graph<V,E>,E> ec) {
				LineArray lineArray = new LineArray(2, LineArray.COORDINATES | LineArray.COLOR_3);
				lineArray.setCoordinates(0, new Point3f[]{new Point3f(0,-.5f,0),new Point3f(0,.5f,0)});
				lineArray.setColor(0, new Color3f(1,1,1));
				lineArray.setColor(1, new Color3f(1,1,1));
				Shape3D shape = new Shape3D();
				shape.setGeometry(lineArray);
				return shape;
//				return new Cylinder(1, 1, 
//						Cylinder.GENERATE_NORMALS |
//						Cylinder.ENABLE_GEOMETRY_PICKING,
//						 26, 26, lightGrayLook);
			}};
		this.vertexAppearanceTransformer = new ConstantTransformer(redLook);
		this.vertexShapeTransformer = new Transformer<V,Node>() {

			public Node transform(V arg0) {
				return new Sphere(10, 
						Sphere.GENERATE_NORMALS | 
						Sphere.ENABLE_GEOMETRY_PICKING|
						Sphere.ENABLE_APPEARANCE_MODIFY, redLook);
			}};
	}
	

	public Transformer<E, Appearance> getEdgeAppearanceTransformer() {
		return edgeAppearanceTransformer;
	}

	public Transformer<Context<Graph<V,E>,E>, Node> getEdgeShapeTransformer() {
		return edgeShapeTransformer;
	}

	public PickedState<E> getPickedEdgeState() {
		return pickedEdgeState;
	}

	public PickedState<V> getPickedVertexState() {
		return pickedVertexState;
	}

	public Transformer<V, Appearance> getVertexAppearanceTransformer() {
		return vertexAppearanceTransformer;
	}

	public Transformer<V, Node> getVertexShapeTransformer() {
		return vertexShapeTransformer;
	}

	public Transformer<V, String> getVertexStringer() {
		return vertexStringer;
	}

	public void setEdgeAppearanceTransformer(Transformer<E, Appearance> edgeAppearanceTransformer) {
		this.edgeAppearanceTransformer = edgeAppearanceTransformer;
		
	}

	public void setEdgeShapeTransformer(Transformer<Context<Graph<V,E>,E>, Node> edgeShapeTransformer) {
		this.edgeShapeTransformer = edgeShapeTransformer;
	}

	public void setPickedEdgeState(PickedState<E> pickedEdgeState) {
			this.pickedEdgeState = pickedEdgeState;
	}

	public void setPickedVertexState(PickedState<V> pickedVertexState) {
		this.pickedVertexState = pickedVertexState;
	}

	public void setVertexAppearanceTransformer(Transformer<V, Appearance> vertexAppearanceTransformer) {
		this.vertexAppearanceTransformer = vertexAppearanceTransformer;
	}

	public void setVertexShapeTransformer(Transformer<V, Node> vertexShapeTransformer) {
		this.vertexShapeTransformer = vertexShapeTransformer;
	}

	public void setVertexStringer(Transformer<V, String> vertexStringer) {
		this.vertexStringer = vertexStringer;
	}
}


