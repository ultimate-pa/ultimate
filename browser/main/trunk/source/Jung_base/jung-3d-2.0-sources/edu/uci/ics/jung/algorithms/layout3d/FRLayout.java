/*
 * Copyright (c) 2003, the JUNG Project and the Regents of the University of
 * California All rights reserved.
 * 
 * This software is open-source under the BSD license; see either "license.txt"
 * or http://jung.sourceforge.net/license.txt for a description.
 */
package edu.uci.ics.jung.algorithms.layout3d;

import java.util.ConcurrentModificationException;
import java.util.HashMap;
import java.util.Map;

import javax.media.j3d.BoundingSphere;
import javax.vecmath.Point3f;
import javax.vecmath.Vector3f;

import org.apache.commons.collections15.Factory;
import org.apache.commons.collections15.map.LazyMap;

import edu.uci.ics.jung.algorithms.util.IterativeContext;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.util.Pair;

/**
 * Implements the Fruchterman-Reingold algorithm for node layout.
 * 
 * @author Scott White, Yan-Biao Boey, Danyel Fisher
 */
public class FRLayout<V, E> extends AbstractLayout<V, E> implements IterativeContext {

    private double forceConstant;

    private double temperature;

    private int currentIteration;

    private int mMaxIterations = 700;
    
//    private Map<V, FRVertexData> frVertexData = 
//    	LazyMap.decorate(new HashMap<V,FRVertexData>(), new Factory<FRVertexData>() {
//    		public FRVertexData create() {
//    			return new FRVertexData();
//    		}});

    private Map<V, Vector3f> frVertexData = 
        LazyMap.decorate(new HashMap<V, Vector3f>(), new Factory<Vector3f>() {
            public Vector3f create() {
                return new Vector3f();
            }});
    
    private double attraction_multiplier = 0.75;
    
    private double attraction_constant;
    
    private double repulsion_multiplier = 0.75;
    
    private double repulsion_constant;
    
    public FRLayout(Graph<V, E> g) {
        super(g);
    }
    
    public FRLayout(Graph<V, E> g, BoundingSphere d) {
        super(g, new RandomLocationTransformer<V>(d), d);
        initialize();
    }
    
    /* (non-Javadoc)
	 * @see edu.uci.ics.jung.visualization.layout.AbstractLayout#setSize(java.awt.Dimension)
	 */
	@Override
	public void setSize(BoundingSphere size) {
		setInitializer(new RandomLocationTransformer<V>(size));
		super.setSize(size);
	}

	public void setAttractionMultiplier(double attraction) {
        this.attraction_multiplier = attraction;
    }
    
    public void setRepulsionMultiplier(double repulsion) {
        this.repulsion_multiplier = repulsion;
    }
    
	public void reset() {
		doInit();
	}
    
    public void initialize() {
    	doInit();
    }

    private void doInit() {
    	Graph<V,E> graph = getGraph();
    	BoundingSphere d = getSize();
    	if(graph != null) {//&& d != null) {
    		currentIteration = 0;
    		temperature = d.getRadius() / 10;

    		forceConstant = 
    			Math
    			.sqrt(d.getRadius()
    					* d.getRadius() * d.getRadius()
    					/ graph.getVertexCount());

    		attraction_constant = attraction_multiplier * forceConstant;
    		repulsion_constant = repulsion_multiplier * forceConstant;
    	}
    }

    private double EPSILON = 0.000001D;

    /**
     * Moves the iteration forward one notch, calculation attraction and
     * repulsion between vertices and edges and cooling the temperature.
     */
    public synchronized void step() {
        currentIteration++;

        /**
         * Calculate repulsion
         */
        while(true) {
            
            try {
                for(V v1 : getGraph().getVertices()) {
//                    if (isLocked(v1)) continue;
                    calcRepulsion(v1);
                }
                break;
            } catch(ConcurrentModificationException cme) {}
        }

        /**
         * Calculate attraction
         */
        while(true) {
            try {
                for(E e : getGraph().getEdges()) {
                    
                    calcAttraction(e);
                }
                break;
            } catch(ConcurrentModificationException cme) {}
        }


        while(true) {
            try {    
                for(V v : getGraph().getVertices()) {
                    if (isLocked(v)) continue;
                    calcPositions(v);
                }
                break;
            } catch(ConcurrentModificationException cme) {}
        }
        cool();
    }

    public synchronized void calcPositions(V v) {
//        FRVertexData fvd = getFRData(v);
        Vector3f fvd = frVertexData.get(v);
        if(fvd == null) return;
        Point3f xyd = transform(v);
        
        double deltaLength = Math.max(EPSILON, fvd.length());
//        double deltaLength = Math.max(EPSILON, Math.sqrt(fvd.disp
//                .dot(fvd.disp)));

        Vector3f newDisp = new Vector3f(fvd);
        newDisp.scale((float)(Math.min(deltaLength, temperature)/deltaLength), fvd);
//        double newXDisp = fvd.getXDisp() / deltaLength
//                * Math.min(deltaLength, temperature);

//        if (Double.isNaN(newXDisp)) { 
//        	throw new IllegalArgumentException(
//                "Unexpected mathematical result in FRLayout:calcPositions [xdisp]"); }
//
//        double newYDisp = fvd.getYDisp() / deltaLength
//                * Math.min(deltaLength, temperature);
//        
//        
//        double newZDisp = fvd.getZDisp() / deltaLength
//                * Math.min(deltaLength, temperature);
//        System.err.println("deltaLength = "+deltaLength);
//        System.err.println(v+" was set to "+xyd);
        
        xyd.add(newDisp);
        
//        xyd.set((float)(xyd.getX()+newXDisp), 
//        		(float)(xyd.getY()+newYDisp), 
//        		(float)(xyd.getZ()+newZDisp));
//        System.err.println("newXDisp="+newXDisp+",newYDisp="+newYDisp+",newZDisp="+newZDisp);
//        System.err.println(v+" set to "+xyd);

        double borderWidth = getSize().getRadius() / 50.0;
        double min = -getSize().getRadius() + borderWidth;
        double max = -min;
        
        double[] min_pos = new double[3];
        double[] max_pos = new double[3];
        for (int i = 0; i < 3; i++)
        {
            min_pos[i] = min + Math.random() * borderWidth * 2;
            max_pos[i] = max - Math.random() * borderWidth * 2;
        }
            
        
        xyd.set((float)Math.min(Math.max(xyd.getX(), min_pos[0]), max_pos[0]), 
                (float)Math.min(Math.max(xyd.getY(), min_pos[1]), max_pos[1]),
                (float)Math.min(Math.max(xyd.getZ(), min_pos[2]), max_pos[2]));
        
//        double newXPos = xyd.getX();
//        if (newXPos < min) {
//            newXPos = min + Math.random() * borderWidth * 2.0;
//        } else if (newXPos > max) {
//            newXPos = max - Math.random()
//                    * borderWidth * 2.0;
//        }
//
//        double newYPos = xyd.getY();
//        if (newYPos < min) {
//            newYPos = min + Math.random() * borderWidth * 2.0;
//        } else if (newYPos > max) {
//            newYPos = max
//                    - Math.random() * borderWidth * 2.0;
//        }
//
//        double newZPos = xyd.getZ();
//        if (newZPos < min) {
//            newZPos = min + Math.random() * borderWidth * 2.0;
//        } else if (newZPos > max) {
//            newZPos = max
//                    - Math.random() * borderWidth * 2.0;
//        }
//
//        xyd.set((float)newXPos, (float)newYPos, (float)newZPos);
    }

    public void calcAttraction(E e) {
        Pair<V> p = getGraph().getEndpoints(e);
        V v1 = p.getFirst();
        V v2 = p.getSecond();
//        V v1 = getGraph().getIncidentVertices(e).iterator().next();
//        V v2 = getGraph().getOpposite(v1, e);
        Point3f p1 = transform(v1);
        Point3f p2 = transform(v2);
        if(p1 == null || p2 == null) return;
//        double xDelta = p1.getX() - p2.getX();
//        double yDelta = p1.getY() - p2.getY();
//        double zDelta = p1.getZ() - p2.getZ();
        
        Vector3f delta = new Vector3f();
        delta.negate(p2); 
        delta.add(p1);
  
        double deltaLength = Math.max(EPSILON, delta.length());

//        double deltaLength = Math.max(EPSILON, Math.sqrt((xDelta * xDelta)
//                + (yDelta * yDelta)));

        double force = (deltaLength * deltaLength) / attraction_constant;

        if (Double.isNaN(force)) { throw new IllegalArgumentException(
                "Unexpected mathematical result in FRLayout:calcPositions [force]"); }

        delta.scale((float)(force / deltaLength));
        
        frVertexData.get(v2).add(delta);
        delta.negate();
        frVertexData.get(v1).add(delta);
        
//        FRVertexData fvd1 = getFRData(v1);
//        FRVertexData fvd2 = getFRData(v2);
//
//        fvd1.decrementDisp(
//        		(float)((xDelta / deltaLength) * force),
//                (float)((yDelta / deltaLength) * force),
//                (float)((zDelta / deltaLength) * force));
//        fvd2.incrementDisp(
//        		(float)((xDelta / deltaLength) * force),
//                (float)((yDelta / deltaLength) * force),
//                (float)((zDelta / deltaLength) * force));
    }

    public void calcRepulsion(V v1) {
        Vector3f fvd1 = frVertexData.get(v1);
//        FRVertexData fvd1 = getFRData(v1);
        if(fvd1 == null) return;
        fvd1.set(0, 0, 0);
//        fvd1.setDisp(0, 0, 0);

        try {
            for(V v2 : getGraph().getVertices()) {

//                if (isLocked(v2)) continue;
                if (v1 != v2) {
                    Point3f p1 = transform(v1);
                    Point3f p2 = transform(v2);
                    if(p1 == null || p2 == null) continue;

//                    double xDelta = p1.getX() - p2.getX();
//                    double yDelta = p1.getY() - p2.getY();
//                    double zDelta = p1.getZ() - p2.getZ();

                    Vector3f delta = new Vector3f();
                    delta.negate(p2); 
                    delta.add(p1);

                    double deltaLength = Math.max(EPSILON, delta.length());

//                    double deltaLength = Math.max(EPSILON, Math
//                            .sqrt((xDelta * xDelta) + (yDelta * yDelta) + (zDelta * zDelta)));
                    
                    double force = (repulsion_constant * repulsion_constant) / deltaLength;
                    
                    if (Double.isNaN(force)) { throw new RuntimeException(
                    "Unexpected mathematical result in FRLayout:calcPositions [repulsion]"); }

                    delta.scale((float)(force / deltaLength));
                    fvd1.add(delta);
                    
//                    fvd1.incrementDisp(
//                    		(float)((xDelta / deltaLength) * force),
//                            (float)((yDelta / deltaLength) * force),
//                            (float)((zDelta / deltaLength) * force));
                }
            }
        } catch(ConcurrentModificationException cme) {
            calcRepulsion(v1);
        }
    }

    private void cool() {
        temperature *= (1.0 - currentIteration / (double) mMaxIterations);
    }

    public void setMaxIterations(int maxIterations) {
        mMaxIterations = maxIterations;
    }

//    public FRVertexData getFRData(V v) {
//        return frVertexData.get(v);
//    }

    /**
     * This one is an incremental visualization.
     */
    public boolean isIncremental() {
        return true;
    }

    /**
     * Returns true once the current iteration has passed the maximum count,
     * <tt>MAX_ITERATIONS</tt>.
     */
    public boolean done() {
        if (currentIteration > mMaxIterations) { 
            return true; 
        } 
        return false;
    }

//    public static class FRVertexData {
//
//        private Vector3f disp;
//
//        public FRVertexData() {
//            initialize();
//        }
//
//        public void initialize() {
//            disp = new Vector3f();
//        }
//
//        public double getXDisp() {
//            return disp.getX();
//        }
//
//        public double getYDisp() {
//            return disp.getY();
//        }
//        
//        public double getZDisp() {
//        	return disp.getZ();
//        }
//
//        public void setDisp(float x, float y, float z) {
//            disp.set(x,y,z);
//        }
//
//        public void incrementDisp(float x, float y, float z) {
//            disp.add(new Vector3f(x,y,z));
//        }
//
//        public void decrementDisp(float x, float y, float z) {
//        	disp.sub(new Vector3f(x,y,x));
//        }
//     }
}