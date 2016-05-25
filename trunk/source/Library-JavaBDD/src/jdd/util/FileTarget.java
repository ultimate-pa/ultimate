
package jdd.util;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;

/** print-target that sends output to a file, used ostly by the tutorials */
public class  FileTarget implements PrintTarget {
	private final PrintStream ps;

	public FileTarget(String filename) throws IOException {
		this(filename, false);
	}

	public FileTarget(String filename, boolean append) throws IOException {
		ps = new PrintStream( new FileOutputStream(filename, append));
	}


	@Override
	public void println(String str) { ps.println(str); }
	@Override
	public void println() { ps.println(); }
	@Override
	public void print(String str) { ps.print(str); }
	@Override
	public void print(char c) { ps.print(c); }

	@Override
	public void flush() { ps.flush(); }
}
