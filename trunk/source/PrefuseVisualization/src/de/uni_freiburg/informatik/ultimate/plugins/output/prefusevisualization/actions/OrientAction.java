package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.actions;

import java.awt.event.ActionEvent;

import javax.swing.AbstractAction;

import prefuse.Constants;
import prefuse.Display;
import prefuse.Visualization;
import prefuse.action.layout.CollapsedSubtreeLayout;
import prefuse.action.layout.graph.NodeLinkTreeLayout;
import prefuse.render.EdgeRenderer;
import prefuse.render.LabelRenderer;

/**
 * manage orientation in current display
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate$
 * $LastChangedBy$
 * $LastChangedRevision$
 */
public class OrientAction extends AbstractAction {

	private static final long serialVersionUID = 1L;
	private int m_orientation;
	private Display m_display;
	private LabelRenderer m_nodeRenderer;
	private EdgeRenderer m_edgeRenderer;
	private Visualization m_vis;

	/**
	 * @param orientation the corrent orientation
	 * @param display the current display
	 * @param nodeRenderer the loaded Note Renderer
	 * @param edgeRenderer the loaded Edge Renderer
	 * @param vis the Visualization running in the display
	 */
	public OrientAction(int orientation, Display display,
			LabelRenderer nodeRenderer, EdgeRenderer edgeRenderer,
			Visualization vis) {
		this.m_orientation = orientation;
		this.m_display = display;
		this.m_nodeRenderer = nodeRenderer;
		this.m_edgeRenderer = edgeRenderer;
		this.m_vis = vis;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
	 */
	public void actionPerformed(ActionEvent evt) {

		setOrientation(m_orientation);
		m_display.getVisualization().cancel("orient");
		m_display.getVisualization().run("treeLayout");
		m_display.getVisualization().run("orient");
	}

	/**
	 * @param orientation
	 */
	public void setOrientation(int orientation) {
		
		NodeLinkTreeLayout rtl = (NodeLinkTreeLayout) m_vis
				.getAction("treeLayout");
		CollapsedSubtreeLayout stl = (CollapsedSubtreeLayout) m_vis
				.getAction("subLayout");
		switch (orientation) {
		case Constants.ORIENT_LEFT_RIGHT:
			m_nodeRenderer.setHorizontalAlignment(Constants.LEFT);
			m_edgeRenderer.setHorizontalAlignment1(Constants.RIGHT);
			m_edgeRenderer.setHorizontalAlignment2(Constants.LEFT);
			m_edgeRenderer.setVerticalAlignment1(Constants.CENTER);
			m_edgeRenderer.setVerticalAlignment2(Constants.CENTER);
			break;
		case Constants.ORIENT_RIGHT_LEFT:
			m_nodeRenderer.setHorizontalAlignment(Constants.RIGHT);
			m_edgeRenderer.setHorizontalAlignment1(Constants.LEFT);
			m_edgeRenderer.setHorizontalAlignment2(Constants.RIGHT);
			m_edgeRenderer.setVerticalAlignment1(Constants.CENTER);
			m_edgeRenderer.setVerticalAlignment2(Constants.CENTER);
			break;
		case Constants.ORIENT_TOP_BOTTOM:
			m_nodeRenderer.setHorizontalAlignment(Constants.CENTER);
			m_edgeRenderer.setHorizontalAlignment1(Constants.CENTER);
			m_edgeRenderer.setHorizontalAlignment2(Constants.CENTER);
			m_edgeRenderer.setVerticalAlignment1(Constants.BOTTOM);
			m_edgeRenderer.setVerticalAlignment2(Constants.TOP);
			break;
		case Constants.ORIENT_BOTTOM_TOP:
			m_nodeRenderer.setHorizontalAlignment(Constants.CENTER);
			m_edgeRenderer.setHorizontalAlignment1(Constants.CENTER);
			m_edgeRenderer.setHorizontalAlignment2(Constants.CENTER);
			m_edgeRenderer.setVerticalAlignment1(Constants.TOP);
			m_edgeRenderer.setVerticalAlignment2(Constants.BOTTOM);
			break;
		case Constants.ORIENT_CENTER:
			m_nodeRenderer.setHorizontalAlignment(Constants.CENTER);
			m_edgeRenderer.setHorizontalAlignment1(Constants.CENTER);
			m_edgeRenderer.setHorizontalAlignment2(Constants.CENTER);
			m_edgeRenderer.setVerticalAlignment1(Constants.CENTER);
			m_edgeRenderer.setVerticalAlignment2(Constants.CENTER);
			break;
		default:
			throw new IllegalArgumentException(
					"Unrecognized orientation value: " + orientation);
		}
		m_orientation = orientation;
		rtl.setOrientation(orientation);
		stl.setOrientation(orientation);
	}

	/**
	 * @return current orientation
	 */
	public int getOrientation() {
		return m_orientation;
	}
}