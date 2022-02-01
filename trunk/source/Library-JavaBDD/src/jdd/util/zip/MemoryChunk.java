

package jdd.util.zip;

/**
 * Memory chunks are used internally by out memory streams to save data of unknown size.
 *
 * <p> note that memory chunks connected used as linked list.
 *
 * @see MemoryInputStream
 * @see MemoryOutputStream
 */

/* package */ class MemoryChunk {
	/**
	 * This is the default size of a chunk.
	 * not too small to be inefficient and not too large to not fit into the memory
	 */
	private static final int CHUNK_SIZE = 1024 * 8;
	/* package */ int size, curr;
	/* package */ byte [] data;
	/* package */ MemoryChunk next;

	/** create an empty memory chunk */
	public MemoryChunk() {
		next = null;
		data = new byte[ size = CHUNK_SIZE];
		curr = 0;
	}

	/**
	 * free this chunk and all the other chunks comming after it (in the linked list)
	 */
	public void free() {
		data = null;
		if(next != null) {
			next.free();
			next = null;
		}
	}

	/** returns true if this chunk is full */
	public boolean full() { return curr >= size; }

	/** insert a new byte in this chunk */
	public void insert(byte b) {
		data[curr++] = b;
	}

	/**
	 * returns the size of the chunk list, strating from here.
	 * that is, it returns the size of this chunk plus the size of the next chunk (if any)
	 * and so on
	 */
	public int getSize() {
		int len = 0;
		MemoryChunk chunk = this;

		do {
			len += chunk.curr;
			chunk = chunk.next;
		} while(chunk != null);
		return len;
	}
}
