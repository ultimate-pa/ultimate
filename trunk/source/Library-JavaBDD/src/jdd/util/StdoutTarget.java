
package jdd.util;

/** this target send everything to stdout (System.out) */
public class StdoutTarget implements PrintTarget {
	public void println(String str) { System.out.println(str); }
	public void println() { System.out.println(); }
	public void print(String str) { System.out.print(str); }
	public void print(char c) { System.out.print(c); }

	public void flush() { System.out.flush(); }
}
