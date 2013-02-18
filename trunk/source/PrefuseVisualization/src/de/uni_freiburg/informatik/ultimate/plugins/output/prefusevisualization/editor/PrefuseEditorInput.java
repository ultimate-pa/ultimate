package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.editor;

import de.uni_freiburg.informatik.ultimate.model.GraphType;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IPersistableElement;

import prefuse.Display;
import prefuse.data.Graph;

/**
 * the edotor input for the prefuse editor
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate$
 * $LastChangedBy$
 * $LastChangedRevision$
 */
public class PrefuseEditorInput implements IEditorInput {
	private Graph m_Graph;
	private GraphType m_GraphType;
	private Display m_Display = null;
	private final String name;

	/**
	 * @param name
	 *            The name of the EditorInput
	 */
	public PrefuseEditorInput(String name) {
		Assert.isNotNull(name);
		this.name = name;
	}

	/**
	 * @param graph
	 *            object for PrefuseVisualization
	 */
	public void setGraph(Graph graph) {
		this.m_Graph = graph;
	}

	/**
	 * @return created graph object for PrefuseVisualization
	 */
	public Graph getGraph() {
		return m_Graph;
	}

	/**
	 * @param Display
	 *            object to show in the PrefuseVisualization
	 */
	public void setDisplay(Display display) {
		this.m_Display = display;
	}

	/**
	 * @return Dispaly object to show in the PrefuseVisualization
	 */
	public Display getDisplay() {
		return m_Display;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.IEditorInput#exists()
	 */
	public boolean exists() {
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.IEditorInput#getImageDescriptor()
	 */
	public ImageDescriptor getImageDescriptor() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.IEditorInput#getName()
	 */
	public String getName() {
		return this.name;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.IEditorInput#getPersistable()
	 */
	public IPersistableElement getPersistable() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.IEditorInput#getToolTipText()
	 */
	public String getToolTipText() {
		return getName();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.core.runtime.IAdaptable#getAdapter(java.lang.Class)
	 */
	@SuppressWarnings("unchecked")
	public Object getAdapter(Class adapter) {
		return null;
	}

	public GraphType getGraphType() {
		return m_GraphType;
	}

	public void setGraphType(GraphType graphType) {
		m_GraphType = graphType;
	}
}