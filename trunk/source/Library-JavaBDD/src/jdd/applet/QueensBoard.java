

package jdd.applet;

import java.awt.BorderLayout;
import java.awt.Canvas;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Frame;
import java.awt.Graphics;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;

import jdd.util.Array;


/** NxN chessboard, used by the N Queens applet*/

public class QueensBoard extends Frame implements WindowListener {
	private final int n;
	private final boolean [] board;

	public QueensBoard(boolean [] b) {

		board = Array.clone(b);
		n = (int)Math.sqrt( board.length);
		final int d = Math.min( 400, n * 50);


		final BoardCanvas c = new BoardCanvas();
		c.setSize( new Dimension(d, d) );
		add( c, BorderLayout.CENTER);

		pack();
		setTitle("" + n + "x" + n + " chessboard");
		setVisible(true);
		addWindowListener( this);
	}

	class BoardCanvas extends Canvas {
		@Override
		public void paint(Graphics g) {
			final Dimension dims = getSize();
			final int h = 1 + dims.height;
			final int w = 1 + dims.width;
			final int d = Math.max( 20, Math.min( h / n, w / n) );

			final int x0 = w - d * n;
			final int y0 = h - d * n;
			g.translate(x0 / 2, y0 / 2);

			g.setColor( Color.black);
			g.drawRect(0,0, n  * d, n * d);

			for(int x = 0; x < n; x++) {
				for(int y = 0; y < n; y++) {
					if( (x + y) % 2 == 0) {
						g.fillRect( x * d, y * d, d, d);
					}
				}
			}

			g.setColor( Color.red);

			final int m = d / 8;
			final int e = d - 2 * m;

			for(int x = 0; x < n; x++) {
				for(int y = 0; y < n; y++) {
					if( board[x + n * y] ) {
						g.fillOval( m + x * d,  m + y * d, e, e);
					}
				}
			}
		}
	}


	@Override
	public void windowActivated(WindowEvent e)  { }
	@Override
	public void windowClosed(WindowEvent e)  { }
	@Override
	public void windowClosing(WindowEvent e)  {setVisible(false); dispose();  }
	@Override
	public void windowDeactivated(WindowEvent e)  { }
	@Override
	public void windowDeiconified(WindowEvent e)  { }
	@Override
	public void windowIconified(WindowEvent e)  { }
	@Override
	public void windowOpened(WindowEvent e)  { }
}

