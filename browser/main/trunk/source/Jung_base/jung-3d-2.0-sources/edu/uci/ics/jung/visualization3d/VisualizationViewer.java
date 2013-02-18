/*
 * Copyright (c) 2003, the JUNG Project and the Regents of the University of
 * California All rights reserved.
 * 
 * This software is open-source under the BSD license; see either "license.txt"
 * or http://jung.sourceforge.net/license.txt for a description.
 */
package edu.uci.ics.jung.visualization3d;

/**
 * 
 */
import java.awt.BorderLayout;
import java.awt.Font;
import java.awt.GraphicsConfiguration;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.util.HashMap;
import java.util.Map;

import javax.media.j3d.AmbientLight;
import javax.media.j3d.Appearance;
import javax.media.j3d.BoundingSphere;
import javax.media.j3d.Bounds;
import javax.media.j3d.BranchGroup;
import javax.media.j3d.Canvas3D;
import javax.media.j3d.DirectionalLight;
import javax.media.j3d.Font3D;
import javax.media.j3d.FontExtrusion;
import javax.media.j3d.Group;
import javax.media.j3d.Material;
import javax.media.j3d.Node;
import javax.media.j3d.OrientedShape3D;
import javax.media.j3d.Text3D;
import javax.media.j3d.Transform3D;
import javax.media.j3d.TransformGroup;
import javax.swing.JPanel;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.vecmath.Color3f;
import javax.vecmath.Point3d;
import javax.vecmath.Point3f;
import javax.vecmath.Vector3f;

import org.apache.commons.collections15.BidiMap;
import org.apache.commons.collections15.bidimap.DualHashBidiMap;

import com.sun.j3d.utils.behaviors.mouse.MouseWheelZoom;
import com.sun.j3d.utils.geometry.Primitive;
import com.sun.j3d.utils.picking.PickTool;
import com.sun.j3d.utils.picking.behaviors.PickingCallback;
import com.sun.j3d.utils.universe.SimpleUniverse;

import edu.uci.ics.jung.algorithms.layout.util.VisRunner;
import edu.uci.ics.jung.algorithms.layout3d.Layout;
import edu.uci.ics.jung.algorithms.util.IterativeContext;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.util.Context;
import edu.uci.ics.jung.graph.util.Pair;
import edu.uci.ics.jung.visualization.picking.MultiPickedState;
import edu.uci.ics.jung.visualization.picking.PickedState;
import edu.uci.ics.jung.visualization3d.control.MouseRotate;
import edu.uci.ics.jung.visualization3d.control.MouseTranslate;
import edu.uci.ics.jung.visualization3d.control.PickSphereBehavior;
import edu.uci.ics.jung.visualization3d.control.PickTranslateBehavior;
import edu.uci.ics.jung.visualization3d.layout.LayoutEventBroadcaster;

/**
 * 
 * @author Tom Nelson - tomnelson@dev.java.net
 *
 */
public class VisualizationViewer<V,E> extends JPanel {

	BranchGroup objRoot;
	TransformGroup objTrans;
//	Appearance vertexLook;
//	Appearance edgeLook;
	Appearance grayLook;
    /**
     * a listener used to cause pick events to result in
     * repaints, even if they come from another view
     */
    protected ItemListener pickEventListener;
	/**
	 * holds the state of which vertices of the graph are
	 * currently 'picked'
	 */
	protected PickedState<V> pickedVertexState;
	
	/**
	 * holds the state of which edges of the graph are
	 * currently 'picked'
	 */
    protected PickedState<E> pickedEdgeState;
    
    protected RenderContext<V,E> renderContext = new PluggableRenderContext<V,E>();

	BidiMap<V,VertexGroup> vertexMap = new DualHashBidiMap<V,VertexGroup>();
	Map<E,EdgeGroup> edgeMap = new HashMap<E,EdgeGroup>();
	Graph<V,E> graph;
	Layout<V,E> layout;

	public VisualizationViewer() {
//		controls = createControls();
		setLayout(new BorderLayout());
		
		renderContext.setPickedVertexState(new MultiPickedState<V>());
		renderContext.setPickedEdgeState(new MultiPickedState<E>());
		GraphicsConfiguration config = 
			SimpleUniverse.getPreferredConfiguration();
		final Canvas3D c = new Canvas3D(config);
		add(c, BorderLayout.CENTER);
		setPickedVertexState(new MultiPickedState<V>());
		setPickedEdgeState(new MultiPickedState<E>());

		// Create a SpringGraph scene and attach it to the virtual universe
		BranchGroup scene = createSceneGraph(c);
		SimpleUniverse u = new SimpleUniverse(c);
		u.getViewer().getView().setUserHeadToVworldEnable(true);	

		// This will move the ViewPlatform back a bit so the
		// objects in the scene can be viewed.
		u.getViewingPlatform().setNominalViewingTransform();

		u.addBranchGraph(scene);
	}
	
	public Layout<V,E> getGraphLayout() {
		return layout;
	}


	public BranchGroup createSceneGraph(final Canvas3D canvas) {

		objRoot = new BranchGroup();
		objRoot.setCapability(Group.ALLOW_CHILDREN_EXTEND);
		objRoot.setCapability(Group.ALLOW_CHILDREN_WRITE);

		TransformGroup objScale = new TransformGroup();
		Transform3D t3d = new Transform3D();
//		t3d.setScale(0.05);
		objScale.setTransform(t3d);
		objRoot.addChild(objScale);

		Transform3D tt = new Transform3D();
		tt.setScale(.05);
		tt.setTranslation(new Vector3f(0, 0, -30.f));
		objTrans = new TransformGroup(tt);
		objTrans.setCapability(TransformGroup.ALLOW_TRANSFORM_WRITE);
		objTrans.setCapability(TransformGroup.ALLOW_TRANSFORM_READ );
		objTrans.setCapability(TransformGroup.ALLOW_CHILDREN_EXTEND);
		objScale.addChild(objTrans);
//		objRoot.addChild(objTrans);

		// Create Colors, Materials,  and Appearances.
		Appearance look = new Appearance();
		Color3f objColor = new Color3f(0.7f, 0.7f, 0.7f);
		Color3f black = new Color3f(0.f, 0.f, 0.f);
		Color3f white = new Color3f(1.0f, 1.0f, 0.6f);
		Color3f gray  = new Color3f(.2f, .2f, .2f);
		Color3f red = new Color3f(1.0f, 0, 0);
		Color3f yellow = new Color3f(1,1,0);
		
		Material objMaterial = new Material(objColor, black,
				objColor, white, 100.0f);
		Material blackMaterial = new Material(objColor, black,
				black, objColor, 10.0f);
		Material whiteMaterial = new Material(white, white,
				white, white, 100.0f);
		Material grayMaterial = new Material(gray, black,
				gray, gray, 100.0f);

		Material redMaterial = new Material(red, black,
				red, red, 100.0f);
		Material yellowMaterial = new Material(yellow, black, 
				yellow, yellow, 100);

		look.setMaterial(new Material(objColor, black,
				objColor, white, 100.0f));
		Appearance blackLook = new Appearance();
		blackLook.setMaterial(blackMaterial);

		Appearance whiteLook = new Appearance();
		whiteLook.setMaterial(whiteMaterial);

		Appearance grayLook = new Appearance();
		grayLook.setMaterial(grayMaterial);
		grayLook.setCapability(Appearance.ALLOW_MATERIAL_READ);
		grayLook.setCapability(Appearance.ALLOW_MATERIAL_WRITE);

		final Appearance redLook = new Appearance();
		redLook.setMaterial(redMaterial);
//		vertexLook = redLook;

		Appearance objLook = new Appearance();
		objLook.setMaterial(objMaterial);
		grayLook = objLook;
		final Appearance yellowLook = new Appearance();
		yellowLook.setMaterial(yellowMaterial);
		Bounds bounds =
			new BoundingSphere(new Point3d(),
					300);

		MouseRotate behavior1 = new MouseRotate();
		behavior1.setTransformGroup(objTrans);
		objTrans.addChild(behavior1);
		behavior1.setSchedulingBounds(bounds);

		MouseWheelZoom behavior2 = new MouseWheelZoom();
		behavior2.setTransformGroup(objTrans);
//		behavior2.setFactor(10);
		objTrans.addChild(behavior2);
		behavior2.setSchedulingBounds(bounds);

		MouseTranslate behavior3 = new MouseTranslate();
		behavior3.setTransformGroup(objTrans);
		objTrans.addChild(behavior3);
		behavior3.setSchedulingBounds(bounds);
		
		PickTranslateBehavior ptb = new PickTranslateBehavior(objRoot,canvas,bounds,PickTool.GEOMETRY);
		ptb.setSchedulingBounds(bounds);
//		objTrans.addChild(ptb);
		ptb.setupCallback(new PickingCallback() {

			public void transformChanged(int type, TransformGroup tg) {
				if(tg == null) return;
				Transform3D t3d = new Transform3D();
				tg.getTransform(t3d);
//				System.err.println(tg+" transformChanged \n"+t3d);
				Point3f p1 = new Point3f();
				V v = vertexMap.getKey(tg);
//				Transform3D lvw = new Transform3D();
//				tg.getLocalToVworld(lvw);
//				System.err.println("lvw = \n"+lvw);
//				lvw.invert();
//				System.err.println("invert lvw = \n"+lvw);
				Point3f p0 = layout.transform(v);
//				Transform3D vwip = new Transform3D();
//				canvas.getVworldToImagePlate(vwip);
//				System.err.println("vwip=\n"+vwip);
//				t3d.mul(lvw);
				t3d.transform(p1);
//				scale.transform(p1);
				System.err.println("change location for vertex "+v+", transformGroup "+tg+" from "+p0+" to "+p1);
//				p1.set(p1.getX()*2,p1.getY()*2,p1.getZ()*2);
//				layout.setLocation(v, p1);
				
			}});
		
		PickSphereBehavior psb = new PickSphereBehavior(objRoot,canvas,bounds);

		PickVertexBehavior pvb = new PickVertexBehavior(objRoot,canvas,bounds,renderContext.getPickedVertexState());
		objTrans.addChild(pvb);
		pvb.addChangeListener(new ChangeListener() {

			public void stateChanged(ChangeEvent e) {
				for(V v : graph.getVertices()) {
					VertexGroup<V> vg = vertexMap.get(v);
					Appearance look = redLook;
					if(renderContext.getPickedVertexState().isPicked(v)) {
						look = yellowLook;
					}
					Node node = vg.getShape();
					if(node instanceof Primitive) {
						((Primitive)node).setAppearance(look);
					}
				}
				
			}});

		//Shine it with two colored lights.
		Color3f lColor1 = new Color3f(.5f, .5f, .5f);
		Color3f lColor2 = new Color3f(1.0f, 1.0f, 1.0f);
		Vector3f lDir2  = new Vector3f(-1.0f, 0.0f, -1.0f);
		DirectionalLight lgt2 = new DirectionalLight(lColor2, lDir2);
		AmbientLight ambient = new AmbientLight(lColor1);
		lgt2.setInfluencingBounds(bounds);
		ambient.setInfluencingBounds(bounds);
		objRoot.addChild(lgt2);
		objRoot.addChild(ambient);
		
		// Let Java 3D perform optimizations on this scene graph.
		objRoot.compile();

//		VisRunner runner = new VisRunner((IterativeContext)elayout);
//		runner.relax();

		return objRoot;
	}
	
	public void setGraphLayout(Layout<V,E> inLayout) {

//		this.layout = inLayout;
		this.graph = inLayout.getGraph();
		BranchGroup branch = new BranchGroup();
		LayoutEventBroadcaster<V,E> elayout =
			new LayoutEventBroadcaster<V,E>(inLayout);
		this.layout = elayout;
		for(V v : graph.getVertices()) {
			VertexGroup<V> vg = new VertexGroup<V>(v, renderContext.getVertexShapeTransformer().transform(v));
			vg.setCapability(TransformGroup.ALLOW_TRANSFORM_WRITE);
			vg.setCapability(TransformGroup.ALLOW_TRANSFORM_READ);
			vertexMap.put(v, vg);
			branch.addChild(vg);
			String label = renderContext.getVertexStringer().transform(v);
			if(label != null) {
				String fontName = "Serif";
				Font3D f3d = new Font3D(new Font(fontName, Font.PLAIN, 2),
						new FontExtrusion());
				Text3D txt = new Text3D(f3d, label, 
						new Point3f(2f,2f,0));
				OrientedShape3D textShape = new OrientedShape3D();
				textShape.setGeometry(txt);
				textShape.setAppearance(grayLook);
//				textShape.setAlignmentAxis( 0.0f, 1.0f, 0.0f);
				textShape.setAlignmentMode(OrientedShape3D.ROTATE_ABOUT_POINT);
				textShape.setRotationPoint(new Point3f());
//				objScale.addChild( textShape );
//				BranchGroup bg = new BranchGroup();
//				bg.addChild(textShape);
//				branch.addChild(bg);
				
				
				
//				Text2D text = new Text2D(label+" more text here", new Color3f(0,0,0),"Serif",50,Font.BOLD);
				Transform3D tt = new Transform3D();
//				tt.setTranslation(new Vector3f(100,100,100));
				tt.setScale(5);
				TransformGroup tg = new TransformGroup(tt);
//				textShape.setGeometry(text);
				tg.addChild(textShape);
				BranchGroup bg = new BranchGroup();
				bg.addChild(tg);
//				branch.addChild(bg);
				vg.getLabelNode().addChild(bg);
				
			}

		}
		System.err.println("vertexMap = "+vertexMap);

		for(E edge : graph.getEdges()) {
			EdgeGroup<E> eg = 
				new EdgeGroup<E>(edge, renderContext.getEdgeShapeTransformer().transform(Context.<Graph<V,E>,E>getInstance(graph, edge)));
			eg.setCapability(TransformGroup.ALLOW_TRANSFORM_WRITE);
			eg.setCapability(TransformGroup.ALLOW_TRANSFORM_READ);
			edgeMap.put(edge, eg);
			branch.addChild(eg);
		}
		
//		System.err.println("branch is "+branch);
//		for(int i=0; i<branch.numChildren(); i++) {
//			System.err.println("branch child ["+i+"] is "+branch.getChild(i));
//		}

		objTrans.addChild(branch);
		elayout.addChangeListener(new ChangeListener() {

			public void stateChanged(ChangeEvent e) {
				for(V v : vertexMap.keySet()) {
					Point3f p = VisualizationViewer.this.layout.transform(v);
					Vector3f pv = new Vector3f(p.getX(), p.getY(), p.getZ());
					Transform3D tx = new Transform3D();
					tx.setTranslation(pv);
					vertexMap.get(v).setTransform(tx);
				}

				for(E edge : graph.getEdges()) {
					Pair<V> endpoints = graph.getEndpoints(edge);
					V start = endpoints.getFirst();
					V end = endpoints.getSecond();
					EdgeGroup eg = edgeMap.get(edge);
					eg.setEndpoints(layout.transform(start), layout.transform(end));
				}
			}});

		elayout.setSize(new BoundingSphere(new Point3d(), 200));
		elayout.initialize();
		VisRunner runner = new VisRunner((IterativeContext)elayout);
		runner.relax();

//		for(int i=0; i<objTrans.numChildren(); i++) {
//			System.err.println("objTrans child ["+i+"] is "+objTrans.getChild(i));
//		}

	}
	
    public void setPickedVertexState(PickedState<V> pickedVertexState) {
        if(pickEventListener != null && this.pickedVertexState != null) {
            this.pickedVertexState.removeItemListener(pickEventListener);
        }
        this.pickedVertexState = pickedVertexState;
        this.renderContext.setPickedVertexState(pickedVertexState);
        if(pickEventListener == null) {
            pickEventListener = new ItemListener() {

                public void itemStateChanged(ItemEvent e) {
                    System.err.println(e.getItem()+" was picked");
                }
            };
        }
        pickedVertexState.addItemListener(pickEventListener);
    }

    /* (non-Javadoc)
     * @see edu.uci.ics.jung.visualization.VisualizationServer#setPickedEdgeState(edu.uci.ics.jung.visualization.picking.PickedState)
     */
    public void setPickedEdgeState(PickedState<E> pickedEdgeState) {
        if(pickEventListener != null && this.pickedEdgeState != null) {
            this.pickedEdgeState.removeItemListener(pickEventListener);
        }
        this.pickedEdgeState = pickedEdgeState;
        this.renderContext.setPickedEdgeState(pickedEdgeState);
        if(pickEventListener == null) {
            pickEventListener = new ItemListener() {

                public void itemStateChanged(ItemEvent e) {
                    repaint();
                }
            };
        }
        pickedEdgeState.addItemListener(pickEventListener);
    }

	/**
	 * @return the renderContext
	 */
	public RenderContext<V, E> getRenderContext() {
		return renderContext;
	}

	
//	public static void main(String argv[])
//	{
//		final VisualizationViewer enigma = new VisualizationViewer();
//		JFrame f = new JFrame();
//		f.add(enigma);
//		f.setSize(600,600);
//		f.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
////			new MainFrame(enigma, 500, 500);
////		f.pack();
//		f.setVisible(true);
//	}
}

