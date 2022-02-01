/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jelena Barth
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2010-2015 pashko
 * 
 * This file is part of the ULTIMATE JungVisualization plug-in.
 * 
 * The ULTIMATE JungVisualization plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE JungVisualization plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE JungVisualization plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE JungVisualization plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE JungVisualization plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.graph;

import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.awt.geom.Point2D;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions.JVContextMenu;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditorInput;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.selection.JungSelection;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.selection.JungSelectionProvider;
import edu.uci.ics.jung.visualization.Layer;
import edu.uci.ics.jung.visualization.MultiLayerTransformer;
import edu.uci.ics.jung.visualization.control.GraphMousePlugin;

/**
 * Checks for mouse clicks on graph nodes an updates the payload information.
 * 
 * @see {@link MouseListener}
 * @see {@link GraphMousePlugin}
 * @author lena
 * 
 */
public class GraphListener implements MouseListener, GraphMousePlugin, MouseMotionListener {

	private Set<VisualizationNode> selectedNodes = null;
	private Set<VisualizationEdge> selectedEdges = null;
	private java.awt.Point mDragpoint;
	private final Set<IElement> mSelectedElements;
	private final JungSelectionProvider mSelectionProvider;
	private final JungEditorInput mEditorInput;

	public GraphListener(final JungSelectionProvider jsp, final JungEditorInput ei) {
		mSelectionProvider = jsp;
		mEditorInput = ei;
		mSelectedElements = new HashSet<IElement>();
	}

	@Override
	public void mouseClicked(final MouseEvent e) {
		if (e.getButton() == MouseEvent.BUTTON3) {
			final JVContextMenu menu = new JVContextMenu(mEditorInput);
			menu.show(e.getComponent(), e.getX(), e.getY());
		}
	}

	@Override
	public void mouseEntered(final MouseEvent e) {
		e.getComponent().getParent().requestFocus();
	}

	@Override
	public void mouseExited(final MouseEvent e) {
	}

	@Override
	public void mousePressed(final MouseEvent e) {
		// If the middle mouse button is pressed, remember the current position of the mouse as a point of reference for
		// panning.
		if (e.getButton() == MouseEvent.BUTTON2) {
			mDragpoint = e.getPoint();
			// Do nothing more when middle mouse button is pressed.
			return;
		}

		// deselect elements
		final Iterator<IElement> elementIt = mSelectedElements.iterator();

		// timing problem while refreshing picked state
		while (elementIt.hasNext()) {

			final IElement currentElement = elementIt.next();

			if (currentElement instanceof VisualizationNode) {
				mEditorInput.getViewer().getPickedVertexState().pick((VisualizationNode) currentElement, false);
			}

		}
	}

	@Override
	public void mouseReleased(final MouseEvent e) {
		// Delete the point of reference for panning when the middle mouse button is released.
		if (e.getButton() == MouseEvent.BUTTON2) {
			mDragpoint = null;
			// Do nothing more when middle mouse button is pressed.
			return;
		}

		// deselect elements
		final Iterator<IElement> elementIt = mSelectedElements.iterator();

		while (elementIt.hasNext()) {

			final IElement currentElement = elementIt.next();

			if (currentElement instanceof VisualizationEdge) {
				mEditorInput.getViewer().getPickedEdgeState().pick((VisualizationEdge) currentElement, false);
			}

		}

		mSelectedElements.clear();

		selectedNodes = mEditorInput.getViewer().getPickedVertexState().getPicked();
		selectedEdges = mEditorInput.getViewer().getPickedEdgeState().getPicked();

		mSelectedElements.addAll(selectedEdges);
		mSelectedElements.addAll(selectedNodes);

		final JungSelection sel = new JungSelection();

		if (!selectedNodes.isEmpty()) {
			// clears the Node View, if more than one node selected

			if (selectedNodes.size() > 1) {
				sel.setElement(null);
			} else // shows Payload, if one node is selected
			{
				final Iterator<VisualizationNode> nodeIt = selectedNodes.iterator();
				final VisualizationNode currentNode = nodeIt.next();
				sel.setElement(currentNode);
			}

			mSelectionProvider.setSelection(sel);
			mSelectionProvider.fireSelectionEvent();
		} else {

			if (selectedEdges.size() == 1) {
				final VisualizationEdge currentEdge = selectedEdges.iterator().next();
				sel.setElement(currentEdge);

			}
			mSelectionProvider.setSelection(sel);
			mSelectionProvider.fireSelectionEvent();

		}

	}

	@Override
	public boolean checkModifiers(final MouseEvent e) {
		return false;
	}

	@Override
	public int getModifiers() {
		return 0;
	}

	@Override
	public void setModifiers(final int modifiers) {
	}

	/**
	 * Accessor method to get Payload of selected nodes.
	 * 
	 * @return A set of selected nodes.
	 */
	public Set<VisualizationNode> getSelectedNodes() {
		return selectedNodes;
	}

	@Override
	/**
	 * Pans the view when the middle mouse button is pressed.
	 */
	public void mouseDragged(final MouseEvent event) {
		if (mDragpoint != null) {
			final MultiLayerTransformer transformer = mEditorInput.getViewer().getRenderContext()
			        .getMultiLayerTransformer();

			final Point2D beginDragPoint = transformer.inverseTransform(Layer.LAYOUT, mDragpoint);
			final Point2D currentDragPoint = transformer.inverseTransform(Layer.LAYOUT, event.getPoint());

			final double delta_x = currentDragPoint.getX() - beginDragPoint.getX();
			final double delta_y = currentDragPoint.getY() - beginDragPoint.getY();

			final double scale = transformer.getTransformer(Layer.VIEW).getScale();

			transformer.getTransformer(Layer.LAYOUT).translate(delta_x * (1 / scale), delta_y * (1 / scale));

			mDragpoint = event.getPoint();
		}
	}

	@Override
	public void mouseMoved(final MouseEvent event) {
	}
}
