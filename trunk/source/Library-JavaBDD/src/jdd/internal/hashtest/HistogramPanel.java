
package jdd.internal.hashtest;



import java.awt.*;

/**
 * GUI component for the histogram class.
 */

public class HistogramPanel extends Panel {
	private static final int PANEL_WIDTH = 640;
	private static final int PANEL_HEIGHT = 128;
	private Histogram histogram;
	private double [] values;
	private double max, chi2, std_dev;

	public HistogramPanel(Histogram histogram) {
		this.histogram = histogram;
		this.values = new double[PANEL_WIDTH];
		this.max = 0.0;

		setBackground( Color.lightGray);
	}

	// ----------------------------------------------------------------------------

	public Dimension getPreferredSize() { return new Dimension(PANEL_WIDTH, PANEL_HEIGHT); }
	public Dimension getMinimumSize() { return getPreferredSize(); }
	public Dimension getMaximumSize() { return getPreferredSize(); }

	// ----------------------------------------------------------------------------
	public void paint(Graphics g) {
		if(max <= 0.0)  g.drawString("no input", 50, 30);
		else {

			g.setColor(Color.red);
			g.drawRect(0,0, PANEL_WIDTH-1, PANEL_HEIGHT-1);
			g.setColor(Color.white);
			for(int i = 0; i < PANEL_WIDTH; i++)
				g.drawLine(i, PANEL_HEIGHT, i, PANEL_HEIGHT - (int) (values[i] * PANEL_HEIGHT / max) );


			g.setColor(Color.black);
			g.drawString("chi^2   = " + chi2, 50,20);
			g.drawString("std-dev = " + std_dev, 50,40);
		}
	}

	public void update() {

		int size = histogram.getSize();
		double size2 = values.length;

		for(int i = 0; i < values.length; i++) values[i] = 0.0;


		for(int i = 0; i < size; i++) {
			int x = histogram.getCount(i);
			double pos = i * size2 / size;

			int pi = (int)pos; pos -= pi;
			values[pi]   += (1 - pos) *x;
			if(pi+1 < PANEL_WIDTH) values[pi+1] += pos * x;
		}

		max = 0;
		for(int i = 0; i < values.length; i++) max = Math.max(max, values[i]);

		chi2 = histogram.getChi2();
		std_dev = histogram.getStandardDeviation();
	}
}
