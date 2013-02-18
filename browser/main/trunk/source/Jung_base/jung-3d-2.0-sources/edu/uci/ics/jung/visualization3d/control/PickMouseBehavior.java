/*
 * $RCSfile: PickMouseBehavior.java,v $
 *
 * Copyright (c) 2006 Sun Microsystems, Inc. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * - Redistribution of source code must retain the above copyright
 *   notice, this list of conditions and the following disclaimer.
 *
 * - Redistribution in binary form must reproduce the above copyright
 *   notice, this list of conditions and the following disclaimer in
 *   the documentation and/or other materials provided with the
 *   distribution.
 *
 * Neither the name of Sun Microsystems, Inc. or the names of
 * contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * This software is provided "AS IS," without a warranty of any
 * kind. ALL EXPRESS OR IMPLIED CONDITIONS, REPRESENTATIONS AND
 * WARRANTIES, INCLUDING ANY IMPLIED WARRANTY OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE OR NON-INFRINGEMENT, ARE HEREBY
 * EXCLUDED. SUN MICROSYSTEMS, INC. ("SUN") AND ITS LICENSORS SHALL
 * NOT BE LIABLE FOR ANY DAMAGES SUFFERED BY LICENSEE AS A RESULT OF
 * USING, MODIFYING OR DISTRIBUTING THIS SOFTWARE OR ITS
 * DERIVATIVES. IN NO EVENT WILL SUN OR ITS LICENSORS BE LIABLE FOR
 * ANY LOST REVENUE, PROFIT OR DATA, OR FOR DIRECT, INDIRECT, SPECIAL,
 * CONSEQUENTIAL, INCIDENTAL OR PUNITIVE DAMAGES, HOWEVER CAUSED AND
 * REGARDLESS OF THE THEORY OF LIABILITY, ARISING OUT OF THE USE OF OR
 * INABILITY TO USE THIS SOFTWARE, EVEN IF SUN HAS BEEN ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGES.
 *
 * You acknowledge that this software is not designed, licensed or
 * intended for use in the design, construction, operation or
 * maintenance of any nuclear facility.
 *
 * $Revision: 1.1 $
 * $Date: 2009/04/08 06:31:15 $
 * $State: Exp $
 */

package edu.uci.ics.jung.visualization3d.control;

import java.awt.AWTEvent;
import java.awt.Event;
import java.awt.event.MouseEvent;
import java.util.Enumeration;

import javax.media.j3d.Behavior;
import javax.media.j3d.Bounds;
import javax.media.j3d.BranchGroup;
import javax.media.j3d.Canvas3D;
import javax.media.j3d.TransformGroup;
import javax.media.j3d.WakeupCriterion;
import javax.media.j3d.WakeupOnAWTEvent;
import javax.media.j3d.WakeupOr;

import com.sun.j3d.utils.picking.PickCanvas;
import com.sun.j3d.utils.picking.PickTool;


/**
 * Base class that allows users to adding picking and mouse manipulation to
 * the scene graph (see PickDragBehavior for an example of how to extend
 * this base class). This class is useful for interactive apps.
 */

public abstract class PickMouseBehavior extends Behavior {
  
  protected PickCanvas pickCanvas;

  protected WakeupCriterion[] conditions;
  protected WakeupOr wakeupCondition;
  protected boolean buttonPress = false;

  protected TransformGroup currGrp;
  protected static final boolean debug = false;
  protected MouseEvent mevent;
  
  /** 
   * Creates a PickMouseBehavior given current canvas, root of the tree to
   * operate on, and the bounds.
   */
  public PickMouseBehavior(Canvas3D canvas, BranchGroup root, Bounds bounds){
    super();
    currGrp = new TransformGroup();
    currGrp.setCapability(TransformGroup.ALLOW_TRANSFORM_WRITE);
    currGrp.setCapability(TransformGroup.ALLOW_TRANSFORM_READ);
    root.addChild(currGrp);
    pickCanvas = new PickCanvas(canvas, root);
  }

  /**
   * Sets the pick mode 
   * @see PickTool#setMode
   **/  
  public void setMode(int pickMode) {
    pickCanvas.setMode(pickMode);
  }

 /**
   * Returns the pickMode
   * @see PickTool#getMode
   */ 

  public int getMode() {
    return pickCanvas.getMode();
  }

  /**
   * Sets the pick tolerance 
   * @see PickCanvas#setTolerance
   */  
  public void setTolerance(float tolerance) {
    pickCanvas.setTolerance(tolerance);
  }

  /**
    * Returns the pick tolerance
    * @see PickCanvas#getTolerance
    */ 
  public float getTolerance() {
    return pickCanvas.getTolerance();
  }

  public void initialize() {

    conditions = new WakeupCriterion[2];
    conditions[0] = new WakeupOnAWTEvent(Event.MOUSE_MOVE);
    conditions[1] = new WakeupOnAWTEvent(Event.MOUSE_DOWN);
    wakeupCondition = new WakeupOr(conditions);

    wakeupOn(wakeupCondition);
  }
  
  private void processMouseEvent(MouseEvent evt) {
    buttonPress = false;

    if (evt.getID()==MouseEvent.MOUSE_PRESSED |
	evt.getID()==MouseEvent.MOUSE_CLICKED) {
      buttonPress = true;
      return;
    }
    else if (evt.getID() == MouseEvent.MOUSE_MOVED) {
      // Process mouse move event
    }
  }
  
  public void processStimulus (Enumeration criteria) {
    WakeupCriterion wakeup;
    AWTEvent[] evt = null;
    int xpos = 0, ypos = 0;

    while(criteria.hasMoreElements()) {
      wakeup = (WakeupCriterion)criteria.nextElement();
      if (wakeup instanceof WakeupOnAWTEvent)
	evt = ((WakeupOnAWTEvent)wakeup).getAWTEvent();
    }
    
    if (evt[0] instanceof MouseEvent){
      mevent = (MouseEvent) evt[0];

      if (debug)
	System.out.println("got mouse event");
      processMouseEvent((MouseEvent)evt[0]);
      xpos = mevent.getPoint().x;
      ypos = mevent.getPoint().y;
    }
    
    if (debug)
      System.out.println("mouse position " + xpos + " " + ypos);
    
    if (buttonPress){
      updateScene(xpos, ypos);
    }
    wakeupOn (wakeupCondition);
  }

  /** Subclasses shall implement this update function 
   */
  public abstract void updateScene(int xpos, int ypos);

}

