/*
 * Copyright (c) 2005, the JUNG Project and the Regents of the University of
 * California All rights reserved.
 *
 * This software is open-source under the BSD license; see either "license.txt"
 * or http://jung.sourceforge.net/license.txt for a description.
 *
 * Created on Aug 5, 2005
 */

package edu.uci.ics.jung.visualization.jai;


/**
 * basic API for implementing perspective transform support
 * 
 * @author Tom Nelson
 *
 */
public interface PerspectiveTransformSupport {

    void activate();
    void deactivate();
    void activate(boolean state);
    PerspectiveShapeTransformer getPerspectiveTransformer();
}