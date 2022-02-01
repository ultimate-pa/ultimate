
package jdd.util.zip;

import java.io.InputStream;

/**
 * a MemoryInputStream is an InputStream that gets its  data from chunks of memory.
 * it is used to save large data to memory instead of file.
 *
 * @see MemoryChunk
 */

public class MemoryInputStream extends InputStream {
	private MemoryChunk root, curr_read;
	private int pos, remaining;
	private final int remaining_save;

	/**
	 * Create a memory stream where read bytes are taken from the given memory chunk
	 */
	public MemoryInputStream(MemoryChunk x) {
		root = curr_read = x;
		pos = 0;
		remaining_save = remaining = x.getSize();
	}

	/**
	 * free the memory occupied by this objects. makes it invalid for subsequent use!
	 */
	public void free() {
		if(root != null) {
			root.free();
		}
		root = curr_read = null;
	}

	/**
	 * is more data available?
	 * @return true the number of available bytes
	 */
	@Override
	public int available() {
		return remaining;
	}

	/**
	 * re-start from the start of the file again
	 */
	@Override
	public void reset() {
		curr_read = root;
		pos = 0;
		remaining = remaining_save;
	}

	/**
	 * read one byte from the stream
	 * @return one byte data or -1 if nothing available
	 * @see #available
	 */
	@Override
	public int read() {
		while( pos >= curr_read.curr) {
			if(curr_read.next == null)
			 {
				return -1; // EOF
			}
			pos = 0;
			curr_read = curr_read.next;
		}

		remaining --;
		return (curr_read.data[pos++]) & 0xFF;
	}
}

