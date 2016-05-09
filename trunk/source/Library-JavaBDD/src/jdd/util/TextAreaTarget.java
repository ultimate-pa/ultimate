

package jdd.util;


import java.awt.*;

/** a print target that directs everything to an AWT TextArea ... */

public class TextAreaTarget implements PrintTarget {
	private TextArea ta;
	public TextAreaTarget(TextArea ta) { this.ta = ta; }
	public void println(String str) { ta.append(str); ta.append("\n"); }
	public void println() { ta.append("\n"); }
	public void print(String str) { ta.append(str); }
	public void print(char c) { ta.append(""+c); }

	public void flush() { /* do nothing */ }
}

