package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.gui;

import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import prefuse.Display;

/**
 * manage the window resize
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate$
 * $LastChangedBy$
 * $LastChangedRevision$ 
 */
public class ResizeAction implements ComponentListener {
		
	private Display m_Display = null;

	private static int m_xSize = 0;
	private static int m_ySize = 0;

	private boolean firstaction = true;

	/**
	 * creates n new resize action
	 * @param display the display to resize
	 */
	public ResizeAction(Display display) {
		m_Display = display;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.awt.event.ComponentListener#componentHidden(java.awt.event.ComponentEvent)
	 */
	//@Override
	public void componentHidden(ComponentEvent e) {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.awt.event.ComponentListener#componentMoved(java.awt.event.ComponentEvent)
	 */
	//@Override
	public void componentMoved(ComponentEvent e) {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.awt.event.ComponentListener#componentResized(java.awt.event.ComponentEvent)
	 */
	//@Override
	public void componentResized(ComponentEvent e) {

		int xSize = e.getComponent().getWidth();
		int ySize = e.getComponent().getHeight();

		ResizeAction.m_xSize = xSize;
		ResizeAction.m_ySize = ySize;

		m_Display.setLocation(0, 0);
		m_Display.setSize(xSize, ySize);

		// move the vis to center
		if (firstaction) {
			m_Display.getVisualization().run("filter");
			firstaction = false;
		} else
			m_Display.getVisualization().run("orient");
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.awt.event.ComponentListener#componentShown(java.awt.event.ComponentEvent)
	 */
	//@Override
	public void componentShown(ComponentEvent e) {
	}

	/**
	 * @return last x-size value
	 */
	public static int getX() {
		return m_xSize;
	}

	/**
	 * @return last x-size value
	 */
	public static int getY() {
		return m_ySize;
	}
}