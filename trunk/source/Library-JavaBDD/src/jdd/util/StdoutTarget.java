
package jdd.util;

/** this target send everything to stdout (System.out) */
public class StdoutTarget implements PrintTarget {
	@Override
	public void println(String str) { System.out.println(str); }
	@Override
	public void println() { System.out.println(); }
	@Override
	public void print(String str) { System.out.print(str); }
	@Override
	public void print(char c) { System.out.print(c); }

	@Override
	public void flush() { System.out.flush(); }
}
