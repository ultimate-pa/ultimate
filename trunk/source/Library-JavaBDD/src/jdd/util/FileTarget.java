
package jdd.util;

import java.io.*;

/** print-target that sends output to a file, used ostly by the tutorials */
public class  FileTarget implements PrintTarget {
	private PrintStream ps;

	public FileTarget(String filename) throws IOException {
		this(filename, false);
	}

	public FileTarget(String filename, boolean append) throws IOException {
		ps = new PrintStream( new FileOutputStream(filename, append));
	}


	public void println(String str) { ps.println(str); }
	public void println() { ps.println(); }
	public void print(String str) { ps.print(str); }
	public void print(char c) { ps.print(c); }

	public void flush() { ps.flush(); }
}
