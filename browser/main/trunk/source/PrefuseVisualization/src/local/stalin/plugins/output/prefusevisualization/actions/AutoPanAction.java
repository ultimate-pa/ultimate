package local.stalin.plugins.output.prefusevisualization.actions;

import java.awt.geom.Point2D;
import java.util.Iterator;

import prefuse.Constants;
import prefuse.Display;
import prefuse.Visualization;
import prefuse.action.Action;
import prefuse.data.tuple.TupleSet;
import prefuse.visual.VisualItem;
import prefuse.data.Tuple;

/**
 * This class controls orientation in display-visualizations.
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate: 2008-03-19 15:47:15 +0100 (Mi, 19. Mär 2008) $
 * $LastChangedBy: keilr $
 * $LastChangedRevision: 509 $
 */
public class AutoPanAction extends Action {
	private Point2D m_start = new Point2D.Double();
	private Point2D m_end = new Point2D.Double();
	private Point2D m_cur = new Point2D.Double();
	private int m_bias = 150;

	private Display m_display;
	private int m_orientation;

	/**
	 * @param display the current display
	 * @param orientation the orientation definied in the display
	 */
	public AutoPanAction(Display display, int orientation) {
		this.m_display = display;
		this.m_orientation = orientation;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see prefuse.action.Action#run(double)
	 */
	public void run(double frac) {

		TupleSet ts = m_vis.getFocusGroup(Visualization.FOCUS_ITEMS);

		if (ts != null) {

			Iterator<?> iteator = ts.tuples();
			if (iteator.hasNext()) {
				Tuple tuple = (Tuple) iteator.next();
				if (tuple.canGetString("type")
						& !tuple.getString("type").equals("edge")) {
					if (ts.getTupleCount() == 0)
						return;

					if (frac == 0.0) {
						int xbias = 0, ybias = 0;
						switch (m_orientation) {
						case Constants.ORIENT_LEFT_RIGHT:
							xbias = m_bias;
							break;
						case Constants.ORIENT_RIGHT_LEFT:
							xbias = -m_bias;
							break;
						case Constants.ORIENT_TOP_BOTTOM:
							ybias = m_bias;
							break;
						case Constants.ORIENT_BOTTOM_TOP:
							ybias = -m_bias;
							break;
						}

						VisualItem vi = (VisualItem) ts.tuples().next();

						m_cur.setLocation(m_display.getWidth() / 2, m_display
								.getHeight() / 2);

						m_display.getAbsoluteCoordinate(m_cur, m_start);

						m_end.setLocation(vi.getX() + xbias, vi.getY() + ybias);

					} else {
						m_cur.setLocation(m_start.getX() + frac
								* (m_end.getX() - m_start.getX()), m_start
								.getY()
								+ frac * (m_end.getY() - m_start.getY()));
						m_display.panToAbs(m_cur);
					}
				}
			}
		}
	}
}