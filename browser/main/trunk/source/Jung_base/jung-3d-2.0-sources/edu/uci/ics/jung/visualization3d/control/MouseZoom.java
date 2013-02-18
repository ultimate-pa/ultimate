/*
 * $RCSfile: MouseZoom.java,v $ Copyright (c) 2006 Sun Microsystems, Inc. All
 * rights reserved. Redistribution and use in source and binary forms, with or
 * without modification, are permitted provided that the following conditions
 * are met: - Redistribution of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer. -
 * Redistribution in binary form must reproduce the above copyright notice, this
 * list of conditions and the following disclaimer in the documentation and/or
 * other materials provided with the distribution. Neither the name of Sun
 * Microsystems, Inc. or the names of contributors may be used to endorse or
 * promote products derived from this software without specific prior written
 * permission. This software is provided "AS IS," without a warranty of any
 * kind. ALL EXPRESS OR IMPLIED CONDITIONS, REPRESENTATIONS AND WARRANTIES,
 * INCLUDING ANY IMPLIED WARRANTY OF MERCHANTABILITY, FITNESS FOR A PARTICULAR
 * PURPOSE OR NON-INFRINGEMENT, ARE HEREBY EXCLUDED. SUN MICROSYSTEMS, INC.
 * ("SUN") AND ITS LICENSORS SHALL NOT BE LIABLE FOR ANY DAMAGES SUFFERED BY
 * LICENSEE AS A RESULT OF USING, MODIFYING OR DISTRIBUTING THIS SOFTWARE OR ITS
 * DERIVATIVES. IN NO EVENT WILL SUN OR ITS LICENSORS BE LIABLE FOR ANY LOST
 * REVENUE, PROFIT OR DATA, OR FOR DIRECT, INDIRECT, SPECIAL, CONSEQUENTIAL,
 * INCIDENTAL OR PUNITIVE DAMAGES, HOWEVER CAUSED AND REGARDLESS OF THE THEORY
 * OF LIABILITY, ARISING OUT OF THE USE OF OR INABILITY TO USE THIS SOFTWARE,
 * EVEN IF SUN HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES. You
 * acknowledge that this software is not designed, licensed or intended for use
 * in the design, construction, operation or maintenance of any nuclear
 * facility. $Revision: 1.1 $ $Date: 2009/04/08 06:31:15 $ $State: Exp $
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
 * MouseZoom is a Java3D behavior object that lets users control the Z axis
 * translation of an object via a mouse drag motion with the second mouse
 * button. See MouseRotate for similar usage info.
 */

public class MouseZoom extends MouseBehavior
{

    double z_factor = .04;
    Vector3d translation = new Vector3d();

    private MouseBehaviorCallback callback = null;

    /**
     * Creates a zoom behavior given the transform group.
     * 
     * @param transformGroup
     *            The transformGroup to operate on.
     */
    public MouseZoom(TransformGroup transformGroup)
    {
        super(transformGroup);
    }

    /**
     * Creates a default mouse zoom behavior.
     */
    public MouseZoom()
    {
        super(0);
    }

    /**
     * Creates a zoom behavior. Note that this behavior still needs a transform
     * group to work on (use setTransformGroup(tg)) and the transform group must
     * add this behavior.
     * 
     * @param flags
     */
    public MouseZoom(int flags)
    {
        super(flags);
    }

    /**
     * Creates a zoom behavior that uses AWT listeners and behavior posts rather
     * than WakeupOnAWTEvent. The behavior is added to the specified Component.
     * A null component can be passed to specify the behavior should use
     * listeners. Components can then be added to the behavior with the
     * addListener(Component c) method.
     * 
     * @param c
     *            The Component to add the MouseListener and MouseMotionListener
     *            to.
     * @since Java 3D 1.2.1
     */
    public MouseZoom(Component c)
    {
        super(c, 0);
    }

    /**
     * Creates a zoom behavior that uses AWT listeners and behavior posts rather
     * than WakeupOnAWTEvent. The behaviors is added to the specified Component
     * and works on the given TransformGroup.
     * 
     * @param c
     *            The Component to add the MouseListener and MouseMotionListener
     *            to. A null component can be passed to specify the behavior
     *            should use listeners. Components can then be added to the
     *            behavior with the addListener(Component c) method.
     * @param transformGroup
     *            The TransformGroup to operate on.
     * @since Java 3D 1.2.1
     */
    public MouseZoom(Component c, TransformGroup transformGroup)
    {
        super(c, transformGroup);
    }

    /**
     * Creates a zoom behavior that uses AWT listeners and behavior posts rather
     * than WakeupOnAWTEvent. The behavior is added to the specified Component.
     * A null component can be passed to specify the behavior should use
     * listeners. Components can then be added to the behavior with the
     * addListener(Component c) method. Note that this behavior still needs a
     * transform group to work on (use setTransformGroup(tg)) and the transform
     * group must add this behavior.
     * 
     * @param flags
     *            interesting flags (wakeup conditions).
     * @since Java 3D 1.2.1
     */
    public MouseZoom(Component c, int flags)
    {
        super(c, flags);
    }

    @Override
    public void initialize()
    {
        super.initialize();
        if ((flags & INVERT_INPUT) == INVERT_INPUT)
        {
            z_factor *= -1;
            invert = true;
        }
    }

    /**
     * Return the y-axis movement multipler.
     */
    public double getFactor()
    {
        return z_factor;
    }

    /**
     * Set the y-axis movement multipler with factor.
     */
    public void setFactor(double factor)
    {
        z_factor = factor;
    }

    public void processStimulus(Enumeration criteria)
    {
        WakeupCriterion wakeup;
        AWTEvent[] events;
        MouseEvent evt;
// int id;
// int dx, dy;

        while (criteria.hasMoreElements())
        {
            wakeup = (WakeupCriterion) criteria.nextElement();
            if (wakeup instanceof WakeupOnAWTEvent)
            {
                events = ((WakeupOnAWTEvent) wakeup).getAWTEvent();
                if (events.length > 0)
                {
                    evt = (MouseEvent) events[events.length - 1];
                    doProcess(evt);
                }
            }

            else if (wakeup instanceof WakeupOnBehaviorPost)
            {
                while (true)
                {
                    synchronized (mouseq)
                    {
                        if (mouseq.isEmpty())
                            break;
                        evt = (MouseEvent) mouseq.remove(0);
                        // consolodate MOUSE_DRAG events
                        while ((evt.getID() == MouseEvent.MOUSE_DRAGGED)
                                && !mouseq.isEmpty()
                                && (((MouseEvent) mouseq.get(0)).getID() == MouseEvent.MOUSE_DRAGGED))
                        {
                            evt = (MouseEvent) mouseq.remove(0);
                        }
                    }
                    doProcess(evt);
                }
            }

        }
        wakeupOn(mouseCriterion);
    }

    void doProcess(MouseEvent evt)
    {
        int id;
        int dx, dy;

        processMouseEvent(evt);

        if (((buttonPress) && ((flags & MANUAL_WAKEUP) == 0))
                || ((wakeUp) && ((flags & MANUAL_WAKEUP) != 0)))
        {
            id = evt.getID();
            if ((id == MouseEvent.MOUSE_DRAGGED) && evt.isAltDown()
                    && !evt.isMetaDown())
            {

                x = evt.getX();
                y = evt.getY();

                dx = x - x_last;
                dy = y - y_last;

                if (!reset)
                {
                    transformGroup.getTransform(currXform);
                    translation.z = dy * z_factor;
                    transformX.set(translation);

                    if (invert)
                    {
                        currXform.mul(currXform, transformX);
                    }
                    else
                    {
                        currXform.mul(transformX, currXform);
                    }

                    transformGroup.setTransform(currXform);

                    transformChanged(currXform);

                    if (callback != null)
                        callback.transformChanged(MouseBehaviorCallback.ZOOM,
                                currXform);
                }
                else
                {
                    reset = false;
                }

                x_last = x;
                y_last = y;
            }
            else if (id == MouseEvent.MOUSE_PRESSED)
            {
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
    public void transformChanged(Transform3D transform)
    {
    }

    /**
     * The transformChanged method in the callback class will
     * be called every time the transform is updated.
     */
    public void setupCallback(MouseBehaviorCallback callback)
    {
        this.callback = callback;
    }
}
