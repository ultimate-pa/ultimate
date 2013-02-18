/*
* Copyright (c) 2003, the JUNG Project and the Regents of the University 
* of California
* All rights reserved.
*
* This software is open-source under the BSD license; see either
* "license.txt" or
* http://jung.sourceforge.net/license.txt for a description.
*/
package edu.uci.ics.jung.algorithms.layout3d;

import java.util.ArrayList;
import java.util.Collection;
import java.util.ConcurrentModificationException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.vecmath.Point3f;
import javax.vecmath.Vector3f;

import org.apache.commons.collections15.Factory;
import org.apache.commons.collections15.map.LazyMap;

import edu.uci.ics.jung.algorithms.util.IterativeContext;
import edu.uci.ics.jung.graph.Graph;

/**
 * Implements a self-organizing map layout algorithm, based on Meyer's
 * self-organizing graph methods.
 * 
 * @author Yan Biao Boey
 */
public class ISOMLayout<V, E> extends AbstractLayout<V,E> implements IterativeContext {

	Map<V, ISOMVertexData> isomVertexData = 
		LazyMap.decorate(new HashMap<V, ISOMVertexData>(),
				new Factory<ISOMVertexData>() {
					public ISOMVertexData create() {
						return new ISOMVertexData();
					}});

	private int maxEpoch;
	private int epoch;

	private int radiusConstantTime;
	private int radius;
	private int minRadius;

	private double adaption;
	private double initialAdaption;
	private double minAdaption;
    
    protected GraphElementAccessor<V,E> elementAccessor = 
    	new RadiusGraphElementAccessor<V,E>();

	private double coolingFactor;

	private List<V> queue = new ArrayList<V>();
	private String status = null;
	
	/**
	 * Returns the current number of epochs and execution status, as a string.
	 */
	public String getStatus() {
		return status;
	}

	public ISOMLayout(Graph<V,E> g) {
		super(g);
	}

	public void initialize() {

		setInitializer(new RandomLocationTransformer<V>(getSize()));
		maxEpoch = 2000;
		epoch = 1;

		radiusConstantTime = 100;
		radius = 5;
		minRadius = 1;

		initialAdaption = 90.0D / 100.0D;
		adaption = initialAdaption;
		minAdaption = 0;

		//factor = 0; //Will be set later on
		coolingFactor = 2;

		//temperature = 0.03;
		//initialJumpRadius = 100;
		//jumpRadius = initialJumpRadius;

		//delay = 100;
	}
	

	/**
	* Advances the current positions of the graph elements.
	*/
	public void step() {
		status = "epoch: " + epoch + "; ";
		if (epoch < maxEpoch) {
			adjust();
			updateParameters();
			status += " status: running";

		} else {
			status += "adaption: " + adaption + "; ";
			status += "status: done";
//			done = true;
		}
	}

	ISOMVertexData tempISOM;
	Point3f tempXYD;

	private synchronized void adjust() {
		//Generate random position in graph space
		tempISOM = new ISOMVertexData();
		tempXYD = new Point3f();

		// creates a new XYZ data location
        tempXYD.set((float)(10 + Math.random() * getSize().getRadius()),
                (float)(10 + Math.random() * getSize().getRadius()),
                (float)(10 + Math.random() * getSize().getRadius()));

		//Get closest vertex to random position
		V winner = elementAccessor.getVertex(this, tempXYD);

		while(true) {
		    try {
		    	for(V v : getGraph().getVertices()) {
		            ISOMVertexData ivd = getISOMVertexData(v);
		            ivd.distance = 0;
		            ivd.visited = false;
		        }
		        break;
		    } catch(ConcurrentModificationException cme) {}
        }
		adjustVertex(winner);
	}

	private synchronized void updateParameters() {
		epoch++;
		double factor = Math.exp(-1 * coolingFactor * (1.0 * epoch / maxEpoch));
		adaption = Math.max(minAdaption, factor * initialAdaption);
		//jumpRadius = (int) factor * jumpRadius;
		//temperature = factor * temperature;
		if ((radius > minRadius) && (epoch % radiusConstantTime == 0)) {
			radius--;
		}
	}

	private synchronized void adjustVertex(V v) {
		queue.clear();
		ISOMVertexData ivd = getISOMVertexData(v);
		ivd.distance = 0;
		ivd.visited = true;
		queue.add(v);
		V current;

		while (!queue.isEmpty()) {
			current = queue.remove(0);
			ISOMVertexData currData = getISOMVertexData(current);
			Point3f currXYData = transform(current);

			double dx = tempXYD.getX() - currXYData.getX();
			double dy = tempXYD.getY() - currXYData.getY();
			double dz = tempXYD.getZ() - currXYData.getZ();
			double factor = adaption / Math.pow(2, currData.distance);
			
			currXYData.set((float)(currXYData.getX()+(factor*dx)), 
					(float)(currXYData.getY()+(factor*dy)),
					(float)(currXYData.getZ()+(factor*dz)));
//			currXYData.addX(factor * dx);
//			currXYData.addY(factor * dy);

			if (currData.distance < radius) {
			    Collection<V> s = getGraph().getNeighbors(current);
			    	//current.getNeighbors();
			    while(true) {
			        try {
			        	for(V child : s) {
//			            for (Iterator iter = s.iterator(); iter.hasNext();) {
//			                Vertex child = (Vertex) iter.next();
			                ISOMVertexData childData = getISOMVertexData(child);
			                if (childData != null && !childData.visited) {
			                    childData.visited = true;
			                    childData.distance = currData.distance + 1;
			                    queue.add(child);
			                }
			            }
			            break;
			        } catch(ConcurrentModificationException cme) {}
			    }
			}
		}
	}

	public ISOMVertexData getISOMVertexData(V v) {
		return isomVertexData.get(v);
	}

	/**
	 * This one is an incremental visualization.
	 * @return <code>true</code> is the layout algorithm is incremental, <code>false</code> otherwise
	 */
	public boolean isIncremental() {
		return true;
	}

	/**
	 * For now, we pretend it never finishes.
	 * @return <code>true</code> is the increments are done, <code>false</code> otherwise
	 */
	public boolean done() {
		return epoch >= maxEpoch;
	}

	public static class ISOMVertexData {
		public Vector3f disp;

		int distance;
		boolean visited;

		public ISOMVertexData() {
			initialize();
		}

		public void initialize() {
			disp = new Vector3f();

			distance = 0;
			visited = false;
		}

		public double getXDisp() {
			return disp.getX();
		}

		public double getYDisp() {
			return disp.getY();
		}

		public double getZDisp() {
			return disp.getZ();
		}

		public void setDisp(double x, double y, double z) {
			disp.set((float)x, (float)y, (float)z);
//			disp.set(1, y);
		}

		public void incrementDisp(double x, double y, double z) {
			disp.add(new Vector3f((float)x, (float)y, (float)z));
//			disp.set(1, disp.get(1) + y);
		}

		public void decrementDisp(double x, double y, double z) {
			disp.sub(new Vector3f((float)x, (float)y, (float)z));
//			disp.set(1, disp.get(1) - y);
		}
	}

	public void reset() {
		epoch = 0;
	}
}