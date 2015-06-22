package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.graph;

import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.awt.geom.Point2D;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions.JVContextMenu;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditorInput;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.selection.JungSelection;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.selection.JungSelectionProvider;

import org.eclipse.jface.viewers.ISelection;

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

	public GraphListener(JungSelectionProvider jsp, JungEditorInput ei) {
		mSelectionProvider = jsp;
		mEditorInput = ei;
		mSelectedElements = new HashSet<IElement>();
	}

	@Override
	public void mouseClicked(MouseEvent e) {
		if (e.getButton() == MouseEvent.BUTTON3) {
			JVContextMenu menu = new JVContextMenu(mEditorInput);
			menu.show(e.getComponent(), e.getX(), e.getY());
		}
	}

	@Override
	public void mouseEntered(MouseEvent e) {
		e.getComponent().getParent().requestFocus();
	}

	@Override
	public void mouseExited(MouseEvent e) {
	}

	@Override
	public void mousePressed(MouseEvent e) {
		// If the middle mouse button is pressed, remember the current position of the mouse as a point of reference for
		// panning.
		if (e.getButton() == MouseEvent.BUTTON2) {
			mDragpoint = e.getPoint();
			// Do nothing more when middle mouse button is pressed.
			return;
		}

		// deselect elements
		Iterator<IElement> elementIt = mSelectedElements.iterator();

		// timing problem while refreshing picked state
		while (elementIt.hasNext()) {

			IElement currentElement = elementIt.next();

			if (currentElement instanceof VisualizationNode) {
				mEditorInput.getViewer().getPickedVertexState().pick((VisualizationNode) currentElement, false);
			}

		}
	}

	@Override
	public void mouseReleased(MouseEvent e) {
		// Delete the point of reference for panning when the middle mouse button is released.
		if (e.getButton() == MouseEvent.BUTTON2) {
			mDragpoint = null;
			// Do nothing more when middle mouse button is pressed.
			return;
		}

		// deselect elements
		Iterator<IElement> elementIt = mSelectedElements.iterator();

		while (elementIt.hasNext()) {

			IElement currentElement = elementIt.next();

			if (currentElement instanceof VisualizationEdge) {
				mEditorInput.getViewer().getPickedEdgeState().pick((VisualizationEdge) currentElement, false);
			}

		}

		mSelectedElements.clear();

		selectedNodes = mEditorInput.getViewer().getPickedVertexState().getPicked();
		selectedEdges = mEditorInput.getViewer().getPickedEdgeState().getPicked();

		mSelectedElements.addAll(selectedEdges);
		mSelectedElements.addAll(selectedNodes);

		JungSelection sel = new JungSelection();

		if (selectedNodes.size() > 0) {
			// clears the Node View, if more than one node selected

			if (selectedNodes.size() > 1) {
				sel.setElement(null);
			} else // shows Payload, if one node is selected
			{
				Iterator<VisualizationNode> nodeIt = selectedNodes.iterator();
				final VisualizationNode currentNode = (VisualizationNode) nodeIt.next();
				sel.setElement(currentNode);
			}

			this.mSelectionProvider.setSelection((ISelection) sel);
			this.mSelectionProvider.fireSelectionEvent();
		} else {

			if (selectedEdges.size() == 1) {
				VisualizationEdge currentEdge = selectedEdges.iterator().next();
				sel.setElement(currentEdge);

			}
			this.mSelectionProvider.setSelection((ISelection) sel);
			this.mSelectionProvider.fireSelectionEvent();

		}

	}

	@Override
	public boolean checkModifiers(MouseEvent e) {
		return false;
	}

	@Override
	public int getModifiers() {
		return 0;
	}

	@Override
	public void setModifiers(int modifiers) {
	}

	/**
	 * Accessor method to get Payload of selected nodes.
	 * 
	 * @return A set of selected nodes.
	 */
	public Set<VisualizationNode> getSelectedNodes() {
		return this.selectedNodes;
	}

	@Override
	/**
	 * Pans the view when the middle mouse button is pressed.
	 */
	public void mouseDragged(MouseEvent event) {
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
	public void mouseMoved(MouseEvent event) {
	}
}
