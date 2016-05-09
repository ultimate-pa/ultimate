

package jdd.applet;

import java.awt.*;
import java.awt.event.*;



import jdd.util.*;


/** NxN chessboard, used by the N Queens applet*/

public class QueensBoard extends Frame implements WindowListener {
	private int n;
	private boolean [] board;

	public QueensBoard(boolean [] b) {

		board = Array.clone(b);
		n = (int)Math.sqrt( board.length);
		int d = Math.min( 400, n * 50);


		BoardCanvas c = new BoardCanvas();
		c.setSize( new Dimension(d, d) );
		add( c, BorderLayout.CENTER);

		pack();
		setTitle("" + n + "x" + n + " chessboard");
		setVisible(true);
		addWindowListener( this);
	}

	class BoardCanvas extends Canvas {
		public void paint(Graphics g) {
			Dimension dims = getSize();
			int h = 1 + dims.height;
			int w = 1 + dims.width;
			int d = Math.max( 20, Math.min( h / n, w / n) );

			int x0 = w - d * n;
			int y0 = h - d * n;
			g.translate(x0 / 2, y0 / 2);

			g.setColor( Color.black);
			g.drawRect(0,0, n  * d, n * d);

			for(int x = 0; x < n; x++) {
				for(int y = 0; y < n; y++) {
					if( (x + y) % 2 == 0)
						g.fillRect( x * d, y * d, d, d);
				}
			}

			g.setColor( Color.red);

			int m = d / 8;
			int e = d - 2 * m;

			for(int x = 0; x < n; x++) {
				for(int y = 0; y < n; y++) {
					if( board[x + n * y] )
						g.fillOval( m + x * d,  m + y * d, e, e);
				}
			}
		}
	}


	public void windowActivated(WindowEvent e)  { }
	public void windowClosed(WindowEvent e)  { }
	public void windowClosing(WindowEvent e)  {setVisible(false); dispose();  }
	public void windowDeactivated(WindowEvent e)  { }
	public void windowDeiconified(WindowEvent e)  { }
	public void windowIconified(WindowEvent e)  { }
	public void windowOpened(WindowEvent e)  { }
}

