
package jdd.util.zip;

import jdd.util.*;
import java.io.*;



/**
 * a MemoryOutputStream is an OutputStream that saves its data to memory-chunks.
 *
 * @see MemoryChunk
 */

public class MemoryOutputStream extends OutputStream {

	private MemoryChunk root, curr_write;


	/**
	 * create a new, empty MemoryOutputStream
	 */

	MemoryOutputStream() {
		root = curr_write = new MemoryChunk();
	}

	/**
	 * write a single byte.
	 * unless the memory is full, this call will never fail
	 */
	public void write(int b) {
		if(curr_write.full()) {
			curr_write.next = new MemoryChunk();
			curr_write = curr_write.next ;
		}
		curr_write.insert( (byte)(b & 0xFF) );
	}

	/**
	 * converts this output stream to an input-stream so that the saved data can be read.
	 * <p>NOTE: after calling this function, the object will become invalid
	 * and cannot be used anymore!
	 */
	public MemoryInputStream convert() {
		MemoryInputStream ret = new MemoryInputStream(root);
		root = curr_write = null; // we are out of work now
		return ret;
	}


	// --------------------------------------------------

	/**
	 * load the contents of a file. appends the read data
	 * into the end of this stream.
	 * @see #save
	 * @return true if it successfully loaded the requested file
	 */
	public boolean load(String name) {
		try {
			FileInputStream fs = new FileInputStream(name);

			byte[] buf = new byte[1024];
			int len;
			while ((len = fs.read(buf)) >= 0) write(buf,0,len);
			fs.close();
			return true;
		} catch(IOException exx) {
			exx.printStackTrace();
		}
		return false;
	}

	/**
	 * save the contents of this stream to a file.
	 *
	 * @see #load
	 * @return true if the operations succeeds
	 */
	public boolean save(String name) {
		try {
			FileOutputStream fs = new FileOutputStream(name);
			MemoryChunk chunk = root;

			do {
				fs.write( chunk.data, 0, chunk.curr);
				chunk = chunk.next;
			} while(chunk != null);
			fs.close();
			return true;
		} catch(IOException exx) {
			exx.printStackTrace();
		}
		return false;
	}
	// --------------------------------------------------

	/** testbench. do not call */
	public static void internal_test() {
		Test.start("MemoryOutputStream");

		MemoryOutputStream mos = new MemoryOutputStream();

		int max = 1024 * 16;
		for(int i = 0; i < max; i++)  mos.write(i);


		MemoryInputStream mis = mos.convert();

		Test.checkEquality(mis.available(), max, "correct byte in buffer");


		int x, c = 0;
		boolean fail = false;
		do {
			x = mis.read();
			if(x != -1 && (x != (c & 0xFF))) fail = true;
			c++;
		} while(x != -1 && !fail);

		Test.check(!fail, "x = (byte)c");
		Test.checkEquality(c, max+1, "correct number of reads");

		Test.end();
	}
}

