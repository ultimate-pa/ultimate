
package jdd.util;

import java.io.*;

/**
 * <pre>
 * The only purpose of this wrapper is to have an inputstream that cannot
 * be closed by that stupid SAX parser [not good if it is a zip stream]
 * </pre>
 */

public class NotCloseableInputStream extends InputStream {
	private InputStream is;

	public NotCloseableInputStream(InputStream is) { this.is = is; }
	public int read() throws IOException { return is.read(); }
	public int read(byte []b) throws IOException { return is.read(b); }
	public int read(byte []b, int o, int s) throws IOException { return is.read(b, o,s); }
	public int available() throws IOException { return is.available() ; }
}
