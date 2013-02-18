/*
 * Created on Jul 19, 2005
 *
 * Copyright (c) 2005, the JUNG Project and the Regents of the University 
 * of California
 * All rights reserved.
 *
 * This software is open-source under the BSD license; see either
 * "license.txt" or
 * http://jung.sourceforge.net/license.txt for a description.
 */
package edu.uci.ics.jung.algorithms.layout3d;

import java.util.Date;
import java.util.Random;

import javax.media.j3d.BoundingSphere;
import javax.vecmath.Point3f;

import org.apache.commons.collections15.Transformer;

/**
 * Transforms the input type into a random location within
 * the bounds of the Dimension property.
 * This is used as the backing Transformer for the LazyMap
 * for many Layouts,
 * and provides a random location for unmapped vertex keys
 * the first time they are accessed.
 * 
 * @author Tom Nelson
 *
 * @param <V>
 */
public class RandomLocationTransformer<V> implements Transformer<V,Point3f> {

	BoundingSphere d;
	Random random;
    
    public RandomLocationTransformer(BoundingSphere d) {
    	this(d, new Date().getTime());
    }
    
    public RandomLocationTransformer(BoundingSphere d, long seed) {
    	this.d = d;
    	this.random = new Random(seed);
    }
    
    private float random() {
    	return (random.nextFloat()*2 - 1) * (float)(d.getRadius());
    }
    
    public Point3f transform(V v) {
    	return new Point3f(random(), random(), random());
    }
}
