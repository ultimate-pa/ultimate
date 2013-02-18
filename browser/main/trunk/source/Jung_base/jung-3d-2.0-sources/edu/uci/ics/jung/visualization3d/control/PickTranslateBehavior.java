/*
 * $RCSfile: PickTranslateBehavior.java,v $
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

import javax.media.j3d.Bounds;
import javax.media.j3d.BranchGroup;
import javax.media.j3d.Canvas3D;
import javax.media.j3d.Transform3D;
import javax.media.j3d.TransformGroup;

import com.sun.j3d.utils.behaviors.mouse.MouseBehavior;
import com.sun.j3d.utils.behaviors.mouse.MouseBehaviorCallback;
import com.sun.j3d.utils.picking.PickResult;
import com.sun.j3d.utils.picking.PickTool;
import com.sun.j3d.utils.picking.behaviors.PickingCallback;

/**
 * A mouse behavior that allows user to pick and translate scene graph objects.
 * Common usage: 1. Create your scene graph. 2. Create this behavior with
 * the root and canvas. See PickRotateBehavior for more details. 
 */

public class PickTranslateBehavior extends PickMouseBehavior implements MouseBehaviorCallback {
	MouseTranslate translate;
	private PickingCallback callback = null;
	private TransformGroup currentTG;

	/**
	 * Creates a pick/translate behavior that waits for user mouse events for
	 * the scene graph. 
	 * @param root   Root of your scene graph.
	 * @param canvas Java 3D drawing canvas.
	 * @param bounds Bounds of your scene.
	 **/

	public PickTranslateBehavior(BranchGroup root, Canvas3D canvas, Bounds bounds){
		super(canvas, root, bounds);
		translate = new MouseTranslate(MouseBehavior.MANUAL_WAKEUP);
		translate.setFactor(1);
		translate.setTransformGroup(currGrp);
		currGrp.addChild(translate);
		translate.setSchedulingBounds(bounds);
		this.setSchedulingBounds(bounds);
	}

	/**
	 * Creates a pick/translate behavior that waits for user mouse events for
	 * the scene graph. 
	 * @param root   Root of your scene graph.
	 * @param canvas Java 3D drawing canvas.
	 * @param bounds Bounds of your scene.
	 * @param pickMode specifys PickTool.BOUNDS, PickTool.GEOMETRY or
	 * PickTool.GEOMETRY_INTERSECT_INFO.  
	 * @see PickTool#setMode
	 **/
	public PickTranslateBehavior(BranchGroup root, Canvas3D canvas,
			Bounds bounds, int pickMode) {
		super(canvas, root, bounds);
		translate = new MouseTranslate(MouseBehavior.MANUAL_WAKEUP);
		translate.setFactor(1);
		translate.setTransformGroup(currGrp);
		currGrp.addChild(translate);
		translate.setSchedulingBounds(bounds);
		this.setSchedulingBounds(bounds);
		this.setMode(pickMode);
	}


	/**
	 * Update the scene to manipulate any nodes. This is not meant to be 
	 * called by users. Behavior automatically calls this. You can call 
	 * this only if you know what you are doing.
	 * 
	 * @param xpos Current mouse X pos.
	 * @param ypos Current mouse Y pos.
	 **/
	public void updateScene(int xpos, int ypos){
//		System.err.println("update scene pick translate");
		TransformGroup tg = null;

		if (!mevent.isAltDown() && !mevent.isMetaDown()){

			pickCanvas.setShapeLocation(xpos, ypos);
			PickResult pr = pickCanvas.pickClosest();
			if ((pr != null) &&
					((tg = (TransformGroup)pr.getNode(PickResult.TRANSFORM_GROUP)) 
							!= null) &&
							(tg.getCapability(TransformGroup.ALLOW_TRANSFORM_READ)) && 
							(tg.getCapability(TransformGroup.ALLOW_TRANSFORM_WRITE))){

				translate.setTransformGroup(tg);
				translate.wakeup();
				currentTG = tg;
				// Need to clean up Issue 123 --- Chien        
				// freePickResult(pr);
			} else if (callback!=null)
				callback.transformChanged( PickingCallback.NO_PICK, null );
		}

	}

	/**
	 * Callback method from MouseTranslate
	 * This is used when the Picking callback is enabled
	 */
	public void transformChanged( int type, Transform3D transform ) {
		callback.transformChanged( PickingCallback.TRANSLATE, currentTG );
	}

	/**
	 * Register the class @param callback to be called each
	 * time the picked object moves
	 */
	public void setupCallback( PickingCallback callback ) {
		this.callback = callback;
		if (callback==null)
			translate.setupCallback( null );
		else
			translate.setupCallback( this );
	}

}

