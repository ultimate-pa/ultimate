
package jdd.internal.hashtest;



import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Panel;

/**
 * GUI component for the histogram class.
 */

public class HistogramPanel extends Panel {
	private static final int PANEL_WIDTH = 640;
	private static final int PANEL_HEIGHT = 128;
	private final Histogram histogram;
	private final double [] values;
	private double max, chi2, std_dev;

	public HistogramPanel(Histogram histogram) {
		this.histogram = histogram;
		values = new double[PANEL_WIDTH];
		max = 0.0;

		setBackground( Color.lightGray);
	}

	// ----------------------------------------------------------------------------

	@Override
	public Dimension getPreferredSize() { return new Dimension(PANEL_WIDTH, PANEL_HEIGHT); }
	@Override
	public Dimension getMinimumSize() { return getPreferredSize(); }
	@Override
	public Dimension getMaximumSize() { return getPreferredSize(); }

	// ----------------------------------------------------------------------------
	@Override
	public void paint(Graphics g) {
		if(max <= 0.0) {
			g.drawString("no input", 50, 30);
		} else {

			g.setColor(Color.red);
			g.drawRect(0,0, PANEL_WIDTH-1, PANEL_HEIGHT-1);
			g.setColor(Color.white);
			for(int i = 0; i < PANEL_WIDTH; i++) {
				g.drawLine(i, PANEL_HEIGHT, i, PANEL_HEIGHT - (int) (values[i] * PANEL_HEIGHT / max) );
			}


			g.setColor(Color.black);
			g.drawString("chi^2   = " + chi2, 50,20);
			g.drawString("std-dev = " + std_dev, 50,40);
		}
	}

	public void update() {

		final int size = histogram.getSize();
		final double size2 = values.length;

		for(int i = 0; i < values.length; i++) {
			values[i] = 0.0;
		}


		for(int i = 0; i < size; i++) {
			final int x = histogram.getCount(i);
			double pos = i * size2 / size;

			final int pi = (int)pos; pos -= pi;
			values[pi]   += (1 - pos) *x;
			if(pi+1 < PANEL_WIDTH) {
				values[pi+1] += pos * x;
			}
		}

		max = 0;
		for(int i = 0; i < values.length; i++) {
			max = Math.max(max, values[i]);
		}

		chi2 = histogram.getChi2();
		std_dev = histogram.getStandardDeviation();
	}
}
