/*
 * $RCSfile: MouseTranslate.java,v $
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

import java.awt.*;
import java.awt.event.*;
import java.util.*;
import javax.media.j3d.*;
import javax.vecmath.*;

import com.sun.j3d.utils.behaviors.mouse.MouseBehavior;
import com.sun.j3d.utils.behaviors.mouse.MouseBehaviorCallback;

/**
 * MouseTranslate is a Java3D behavior object that lets users control the 
 * translation (X, Y) of an object via a mouse drag motion with the third
 * mouse button (alt-click on PC). See MouseRotate for similar usage info.
 */

public class MouseTranslate extends MouseBehavior {

	double x_factor = .02;
	double y_factor = .02;
	Vector3d translation = new Vector3d();

	private MouseBehaviorCallback callback = null;

	/**
	 * Creates a mouse translate behavior given the transform group.
	 * @param transformGroup The transformGroup to operate on.
	 */
	public MouseTranslate(TransformGroup transformGroup) {
		super(transformGroup);
	}

	/**
	 * Creates a default translate behavior.
	 */
	public MouseTranslate(){
		super(0);
	}

	/**
	 * Creates a translate behavior.
	 * Note that this behavior still needs a transform
	 * group to work on (use setTransformGroup(tg)) and
	 * the transform group must add this behavior.
	 * @param flags
	 */
	public MouseTranslate(int flags) {
		super(flags);
	}

	/**
	 * Creates a translate behavior that uses AWT listeners and behavior
	 * posts rather than WakeupOnAWTEvent.  The behavior is added to the
	 * specified Component. A null component can be passed to specify
	 * the behavior should use listeners.  Components can then be added
	 * to the behavior with the addListener(Component c) method.
	 * @param c The Component to add the MouseListener
	 * and MouseMotionListener to.
	 * @since Java 3D 1.2.1
	 */
	public MouseTranslate(Component c) {
		super(c, 0);
	} 

	/**
	 * Creates a translate behavior that uses AWT listeners and behavior
	 * posts rather than WakeupOnAWTEvent.  The behaviors is added to
	 * the specified Component and works on the given TransformGroup.
	 * A null component can be passed to specify the behavior should use
	 * listeners.  Components can then be added to the behavior with the
	 * addListener(Component c) method.
	 * @param c The Component to add the MouseListener and
	 * MouseMotionListener to.
	 * @param transformGroup The TransformGroup to operate on.
	 * @since Java 3D 1.2.1
	 */
	public MouseTranslate(Component c, TransformGroup transformGroup) {
		super(c, transformGroup);
	}

	/**
	 * Creates a translate behavior that uses AWT listeners and behavior
	 * posts rather than WakeupOnAWTEvent.  The behavior is added to the
	 * specified Component.  A null component can be passed to specify
	 * the behavior should use listeners.  Components can then be added to
	 * the behavior with the addListener(Component c) method.
	 * Note that this behavior still needs a transform
	 * group to work on (use setTransformGroup(tg)) and the transform
	 * group must add this behavior.
	 * @param flags interesting flags (wakeup conditions).
	 * @since Java 3D 1.2.1
	 */
	public MouseTranslate(Component c, int flags) {
		super(c, flags);
	}

	public void initialize() {
		super.initialize();
		if ((flags & INVERT_INPUT) == INVERT_INPUT) {
			invert = true;
			x_factor *= -1;
			y_factor *= -1;
		}
	}

	/**
	 * Return the x-axis movement multipler.
	 **/
	public double getXFactor() {
		return x_factor;
	}

	/**
	 * Return the y-axis movement multipler.
	 **/
	public double getYFactor() {
		return y_factor;
	}

	/**
	 * Set the x-axis amd y-axis movement multipler with factor.
	 **/
	public void setFactor( double factor) {
		x_factor = y_factor = factor;
	}

	/**
	 * Set the x-axis amd y-axis movement multipler with xFactor and yFactor
	 * respectively.
	 **/
	public void setFactor( double xFactor, double yFactor) {
		x_factor = xFactor;
		y_factor = yFactor;    
	}

	public void processStimulus (Enumeration criteria) {
		WakeupCriterion wakeup;
		AWTEvent[] events;
		MouseEvent evt;
//		int id;
//		int dx, dy;

		while (criteria.hasMoreElements()) {
			wakeup = (WakeupCriterion) criteria.nextElement();

			if (wakeup instanceof WakeupOnAWTEvent) {
				events = ((WakeupOnAWTEvent)wakeup).getAWTEvent();
				if (events.length > 0) {
					evt = (MouseEvent) events[events.length-1];
					doProcess(evt);
				}
			}

			else if (wakeup instanceof WakeupOnBehaviorPost) {
				while (true) {
					// access to the queue must be synchronized
					synchronized (mouseq) {
						if (mouseq.isEmpty()) break;
						evt = (MouseEvent)mouseq.remove(0);
						// consolodate MOUSE_DRAG events
						while ((evt.getID() == MouseEvent.MOUSE_DRAGGED) &&
								!mouseq.isEmpty() &&
								(((MouseEvent)mouseq.get(0)).getID() ==
									MouseEvent.MOUSE_DRAGGED)) {
							evt = (MouseEvent)mouseq.remove(0);
						}
					}
					doProcess(evt);
				}
			}

		}
		wakeupOn(mouseCriterion);
	}

	void doProcess(MouseEvent evt) {
		int id;
		int dx, dy;

		processMouseEvent(evt);

		if (((buttonPress)&&((flags & MANUAL_WAKEUP) == 0)) ||
				((wakeUp)&&((flags & MANUAL_WAKEUP) != 0))){
			id = evt.getID();
			if ((id == MouseEvent.MOUSE_DRAGGED) &&
					!evt.isAltDown() && !evt.isMetaDown()) {

				x = evt.getX();
				y = evt.getY();

				dx = x - x_last;
				dy = y - y_last;

				if ((!reset) && ((Math.abs(dy) < 50) && (Math.abs(dx) < 50))) {
					//System.out.println("dx " + dx + " dy " + dy);
					transformGroup.getTransform(currXform);
					
					
//					System.err.println("currXform is \n"+currXform);
					Transform3D origCurrentXform = new Transform3D(currXform);
					
					Transform3D ltvw = new Transform3D();
					transformGroup.getLocalToVworld(ltvw);
//					System.err.println("ltvw is \n"+ltvw);
					Matrix3d mat = new Matrix3d();
					ltvw.getRotationScale(mat);
					Transform3D rot = new Transform3D();
					rot.set(mat);
//					x_factor = y_factor = 1/ltvw.getScale();
					
//					currXform.mulInverse(origCurrentXform);
//					currXform.mul(rot);
					
					
//					System.err.println("after mul. currXform is \n"+currXform);
//					Transform3D scale = new Transform3D();
//					scale.setScale(ltvw.getScale());
//					scale.invert();
//					rot.mul(scale);
					
					
					
					translation.x = dx*x_factor; 
					translation.y = -dy*y_factor;
					
					
//					Vector3d translationOut = new Vector3d();
//					rot.transform(translation, translationOut);

					transformX.set(translation);

					if (invert) {
						currXform.mul(currXform, transformX);
					} else {
						currXform.mul(transformX, currXform);
					}

//					currXform.mulInverse(rot);
//					currXform.mul(origCurrentXform);
					transformGroup.setTransform(currXform);

					transformChanged( currXform );

					if (callback!=null)
						callback.transformChanged( MouseBehaviorCallback.TRANSLATE,
								currXform );

				}
				else {
					reset = false;
				}
				x_last = x;
				y_last = y;
			}
			else if (id == MouseEvent.MOUSE_PRESSED) {
				x_last = evt.getX();
				y_last = evt.getY();
			}
		}
	}

	/**
	 * Users can overload this method  which is called every time
	 * the Behavior updates the transform
	 *
	 * Default implementation does nothing
	 */
	public void transformChanged( Transform3D transform ) {
	}

	/**
	 * The transformChanged method in the callback class will
	 * be called every time the transform is updated
	 */
	public void setupCallback( MouseBehaviorCallback callback ) {
		this.callback = callback;
	}
}

