
package jdd.util;

import java.io.IOException;
import java.io.InputStream;

/**
 * <pre>
 * The only purpose of this wrapper is to have an inputstream that cannot
 * be closed by that stupid SAX parser [not good if it is a zip stream]
 * </pre>
 */

public class NotCloseableInputStream extends InputStream {
	private final InputStream is;

	public NotCloseableInputStream(InputStream is) { this.is = is; }
	@Override
	public int read() throws IOException { return is.read(); }
	@Override
	public int read(byte []b) throws IOException { return is.read(b); }
	@Override
	public int read(byte []b, int o, int s) throws IOException { return is.read(b, o,s); }
	@Override
	public int available() throws IOException { return is.available() ; }
}
