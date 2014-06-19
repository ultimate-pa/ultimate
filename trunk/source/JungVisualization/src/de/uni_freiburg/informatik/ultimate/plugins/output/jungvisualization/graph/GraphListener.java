package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.graph;

import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions.JVContextMenu;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.selection.JungSelection;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.selection.JungSelectionProvider;

import org.eclipse.jface.viewers.ISelection;

import edu.uci.ics.jung.visualization.control.GraphMousePlugin;

/**
 * Checks for mouse clicks on graph nodes an updates the payload information.
 * @see {@link MouseListener}
 * @see {@link GraphMousePlugin}
 * @author lena
 *
 */
public class GraphListener implements MouseListener, GraphMousePlugin {
	
	private Set<VisualizationNode> selectedNodes = null;
	private Set<VisualizationEdge> selectedEdges = null;
	Set<IElement> selectedElements = null;
    private JungSelectionProvider jsp;
    
    public GraphListener(JungSelectionProvider jsp){
    	this.jsp = jsp;
    	selectedElements = new HashSet<IElement>();
    }
	
	/*
	 * (non-Javadoc)
	 * @see java.awt.event.MouseListener#mouseClicked(java.awt.event.MouseEvent)
	 */
	@Override
	public void mouseClicked(MouseEvent e) {
		if (e.getButton() == MouseEvent.BUTTON3)
		{	
			JVContextMenu menu = new JVContextMenu();
			menu.show(e.getComponent(), e.getX(), e.getY());
		}
		
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.awt.event.MouseListener#mouseEntered(java.awt.event.MouseEvent)
	 */
	@Override
	public void mouseEntered(MouseEvent e) {
		e.getComponent().getParent().requestFocus();
	}

	/*
	 * (non-Javadoc)
	 * @see java.awt.event.MouseListener#mouseExited(java.awt.event.MouseEvent)
	 */
	@Override
	public void mouseExited(MouseEvent e) {
	}

	/*
	 * (non-Javadoc)
	 * @see java.awt.event.MouseListener#mousePressed(java.awt.event.MouseEvent)
	 */
	@Override
	public void mousePressed(MouseEvent e) {
		//deselect elements
		Iterator<IElement> elementIt = selectedElements.iterator();
		
		//timing problem while refreshing picked state
		while (elementIt.hasNext()){
			
			IElement currentElement = elementIt.next();
			
			if (currentElement instanceof VisualizationNode){
				GraphHandler.getInstance().getVisualizationViewer().getPickedVertexState().pick((VisualizationNode)currentElement, false);
			}
//			else
//			{
//				GraphHandler.getInstance().getVisualizationViewer().getPickedEdgeState().pick((VisualizationEdge)currentElement, false);
//			}
			
		}
		
		//selectedElements.clear();
		
	}

	/*
	 * @see java.awt.event.MouseListener#mouseReleased(java.awt.event.MouseEvent)
	 */
	@Override
	public void mouseReleased(MouseEvent e) {
		//deselect elements
		Iterator<IElement> elementIt = selectedElements.iterator();
		
		while (elementIt.hasNext()){
			
			IElement currentElement = elementIt.next();
			
//			if (currentElement instanceof VisualizationNode){
//				GraphHandler.getInstance().getVisualizationViewer().getPickedVertexState().pick((VisualizationNode)currentElement, false);
//			}
//			else
			if (currentElement instanceof VisualizationEdge)
			{
				GraphHandler.getInstance().getVisualizationViewer().getPickedEdgeState().pick((VisualizationEdge)currentElement, false);
			}
			
		}
		
		selectedElements.clear();
		
		
		selectedNodes = GraphHandler.getInstance().getVisualizationViewer().getPickedVertexState().getPicked();
		selectedEdges = GraphHandler.getInstance().getVisualizationViewer().getPickedEdgeState().getPicked();
		
		selectedElements.addAll(selectedEdges);
		selectedElements.addAll(selectedNodes);
				
		JungSelection sel = new JungSelection();
		
		if (selectedNodes.size() > 0) {	
			//clears the Node View, if more than one node selected

			if (selectedNodes.size() > 1){
				sel.setElement(null);
			}
			else //shows Payload, if one node is selected
			{
				Iterator<VisualizationNode> nodeIt = selectedNodes.iterator();
				final VisualizationNode currentNode = (VisualizationNode) nodeIt.next();
				sel.setElement(currentNode);
			}
			
			this.jsp.setSelection((ISelection) sel);
			this.jsp.fireSelectionEvent();
		}
		else{ 
			
			if (selectedEdges.size() == 1){
		    VisualizationEdge currentEdge = selectedEdges.iterator().next();
			sel.setElement(currentEdge);
			
			}
			this.jsp.setSelection((ISelection) sel);
			this.jsp.fireSelectionEvent();
			
		}
		
	}

	/*
	 * (non-Javadoc)
	 * @see edu.uci.ics.jung.visualizationr.control.GraphMousePlugin#checkModifiers(java.awt.event.MouseEvent)
	 */
	@Override
	public boolean checkModifiers(MouseEvent e) {
		return false;
	}

	/*
	 * (non-Javadoc)
	 * @see edu.uci.ics.jung.visualization.control.GraphMousePlugin#getModifiers()
	 */
	@Override
	public int getModifiers() {
		// TODO Auto-generated method stub
//		System.out.println("NodeListener.getModifiers ausgelöst.");//doesn't fire
		return 0;
	}

	/*
	 * (non-Javadoc)
	 * @see edu.uci.ics.jung.visualization.control.GraphMousePlugin#setModifiers(int)
	 */
	@Override
	public void setModifiers(int modifiers) {
		// TODO Auto-generated method stub
//		System.out.println("NodeListener.setModifiers ausgelöst.");//doesn't fire
	}

	/**
	 * Accessor method to get Payload of selected nodes.
	 *
	 * @return A set of selected nodes.
	 */
	public Set<VisualizationNode> getSelectedNodes() {
		return this.selectedNodes;
	}
}
