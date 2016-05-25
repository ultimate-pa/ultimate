

package jdd.util;


import java.awt.TextArea;

/** a print target that directs everything to an AWT TextArea ... */

public class TextAreaTarget implements PrintTarget {
	private final TextArea ta;
	public TextAreaTarget(TextArea ta) { this.ta = ta; }
	@Override
	public void println(String str) { ta.append(str); ta.append("\n"); }
	@Override
	public void println() { ta.append("\n"); }
	@Override
	public void print(String str) { ta.append(str); }
	@Override
	public void print(char c) { ta.append(""+c); }

	@Override
	public void flush() { /* do nothing */ }
}

