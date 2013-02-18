package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.gui;

import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.selection.PrefuseSelectionProvider;

import java.awt.Color;
import java.awt.event.MouseEvent;

import prefuse.Display;
import prefuse.Visualization;
import prefuse.controls.ControlAdapter;
import prefuse.controls.DragControl;
import prefuse.controls.FocusControl;
import prefuse.controls.NeighborHighlightControl;
import prefuse.controls.PanControl;
import prefuse.controls.WheelZoomControl;
import prefuse.controls.ZoomControl;
import prefuse.controls.ZoomToFitControl;

import prefuse.visual.VisualItem;
import javax.swing.JPanel;


/**
 * the panel in witch prefuse paints the display object
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate$
 * $LastChangedBy$
 * $LastChangedRevision$ 
 */
public class PrefusePanel extends JPanel {

	private static final long serialVersionUID = 1L;
	protected static final String VisualItem = null;
	private static PrefuseColorSelection m_Ipcs = new PrefuseColorSelection();
	private static VisualItem m_LastClicked = null;
	private PrefuseSelectionProvider m_SelectionPrivider;

	/**
	 * @param gview
	 *            the Display for visualization
	 * @param label
	 *            label of the panel
	 * @param root
	 *            the root of the graph
	 */
	public PrefusePanel(final Display gview, final String label) {

		Visualization vis = gview.getVisualization();
		vis.run("filter");

		gview.addControlListener(new ControlAdapter() {

			/*
			 * (non-Javadoc)
			 * 
			 * @see prefuse.controls.ControlAdapter#itemClicked(prefuse.visual.VisualItem,
			 *      java.awt.event.MouseEvent)
			 */
			public void itemClicked(VisualItem item, MouseEvent e) {

				m_LastClicked = item;
gview.requestFocus();
				if (item.canGetString("uid")) {

					String uid = item.getString("uid");
					m_SelectionPrivider.itemClicked(uid);
				} else {
					m_SelectionPrivider.itemClicked();
				}

				item.setTextColor(m_Ipcs.getTextMarkColor(item.getSourceTuple()
						.getString("name")));
				item.setFillColor(m_Ipcs.getNodeMarkColor(item.getSourceTuple()
						.getString("name")));
				repaint();
			}

			/*
			 * (non-Javadoc)
			 * 
			 * @see prefuse.controls.Contr;olAdapter#itemEntered(prefuse.visual.VisualItem,
			 *      java.awt.event.MouseEvent)
			 */
			public void itemEntered(VisualItem item, MouseEvent e) {
				if (item != m_LastClicked) {
					item.setTextColor(m_Ipcs.getTextOverColor(item
							.getSourceTuple().getString("name")));
					item.setFillColor(m_Ipcs.getNodeOverColor(item
							.getSourceTuple().getString("name")));
					repaint();
				}
			}

			/*
			 * (non-Javadoc)
			 * 
			 * @see prefuse.controls.ControlAdapter#itemExited(prefuse.visual.VisualItem,
			 *      java.awt.event.MouseEvent)
			 */
			public void itemExited(VisualItem item, MouseEvent e) {
				if (item != m_LastClicked) {
					item.setTextColor(m_Ipcs.getTextStyleColor(item
							.getSourceTuple().getString("name")));
					item.setFillColor(m_Ipcs.getNodeStyleColor(item
							.getSourceTuple().getString("name")));
					repaint();
				}
			}

		});

		// main display controls
		gview.addControlListener(new FocusControl(1));
		gview.addControlListener(new DragControl());
		gview.addControlListener(new PanControl());
		gview.addControlListener(new ZoomControl());
		gview.addControlListener(new WheelZoomControl());
		gview.addControlListener(new ZoomToFitControl());
		gview.addControlListener(new NeighborHighlightControl());

		add(gview);

		Color BACKGROUND = Color.WHITE;
		Color FOREGROUND = Color.BLACK;

		gview.setBackground(BACKGROUND);
		gview.setForeground(FOREGROUND);
	}

	/**
	 * @param prefuseSelectionProvider
	 *            the SelectionProvider to fire the selection event
	 */
	public void addSelectionListener(
			PrefuseSelectionProvider prefuseSelectionProvider) {
		m_SelectionPrivider = prefuseSelectionProvider;
	}

	public static VisualItem getLastClickedItem() {
		return m_LastClicked;
	}
}