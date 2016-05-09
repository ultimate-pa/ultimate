
package jdd.util;

/**
 * handles all allocation of *DD related large arrays.
 * This way, we can keep track of the allocated memory during the lifetime of JDD.
 */

public class Allocator {
	private static long int_s = 0, int_c = 0, short_s = 0, short_c = 0, double_c = 0;
	private static long char_s = 0, char_c = 0, byte_s = 0, byte_c = 0, double_s = 0;
	private static long int_t = 0, short_t = 0, char_t = 0, byte_t = 0, double_t = 0;


	/** This function is called when memory allocation fails */
	private static void fail(long size, String type, OutOfMemoryError ex) {
		ex.printStackTrace();
		JDDConsole.out.print("FAILED to allocate " + size + " bytes (" );
		jdd.util.math.Digits.printNumber1024(size);
		JDDConsole.out.println(") for an " + type+"[]");
		JDDConsole.out.println("Allocator statistics so far:");
		showStats();
		throw ex;
		// System.exit(20);
	}

	// --------------------------------------------------------------------

	/** allocate an array of integers */
	public static int [] allocateIntArray(int size) {

		if(int_s < size) int_s = size;
		int_c ++;
		int_t += size;
		try {
			// System.gc();
			return new int[size];
		} catch(OutOfMemoryError ex) {fail(size*4L,"int",ex);return null;}
	}

	/** allocate an array of double precision floating points */
	public static double [] allocateDoubleArray(int size) {

		if(double_s < size) double_s = size;
		double_c ++;
		double_t += size;
		try {
			// System.gc();
			return new double[size];
		} catch(OutOfMemoryError ex) {fail(size*8L,"double",ex);return null;}
	}


	/** allocate an array of short integers */
	public static short [] allocateShortArray(int size) {
		if(short_s < size) short_s = size;
		short_c ++;
		short_t += size;
		try {
			// System.gc();
			return new short[size];
		} catch(OutOfMemoryError ex) {fail(size*2L,"short",ex);return null;}
	}

	/** allocate an array of chars */
	public static char [] allocateCharArray(int size) {
		if(char_s < size) char_s = size;
		char_c ++;
		char_t += size;
		try {
			// System.gc();
			return new char[size];
		} catch(OutOfMemoryError ex) {fail(size*2L,"char",ex);return null;}
	}

	/** allocate an array of bytes */
	public static byte [] allocateByteArray(int size) {
		if(byte_s < size) byte_s = size;
		byte_c ++;
		byte_t += size;
		try {
			// System.gc();
			return new byte[size];
		} catch(OutOfMemoryError ex) {fail(size,"byte",ex);return null;}
	}

	/** allocate an array of boolean */
	public static boolean [] allocateBooleanArray(int size) {
		// NO statistics yet
		return new boolean[size];
	}

	/** show the current memory allocation statistics */
	public static void showStats() {
		JDDConsole.out.print("Allocator , total mem: " + (int_t * 4 + short_t * 4 + char_t * 2 + byte_t));
		JDDConsole.out.println(", stats (type,count,max,total):");
		if(int_c > 0) JDDConsole.out.print( "(int," + int_c + "," + int_s + "," + int_t + ")");
		if(short_c > 0) JDDConsole.out.print( " (short," + short_c + "," + short_s + "," + short_t + ")");
		if(char_c > 0) JDDConsole.out.print( " (char," + char_c + "," + char_s + "," + char_t + ")");
		if(byte_c > 0) JDDConsole.out.print( " (byte," + byte_c + "," + byte_s + "," + byte_t + ")");
		if(double_c > 0) JDDConsole.out.print( " (double," + double_c + "," + double_s + "," + double_t + ")");
		JDDConsole.out.println();

		JDDConsole.out.print("Total / Max / Used / Free memory: ");
		jdd.util.math.Digits.printNumber1024( jdd.util.jre.JREInfo.totalMemory() );	JDDConsole.out.print("/ ");
		jdd.util.math.Digits.printNumber1024( jdd.util.jre.JREInfo.maxMemory() );	JDDConsole.out.print("/ ");
		jdd.util.math.Digits.printNumber1024( jdd.util.jre.JREInfo.usedMemory() );	JDDConsole.out.print("/ ");
		jdd.util.math.Digits.printNumber1024( jdd.util.jre.JREInfo.freeMemory() );
		JDDConsole.out.println();
	}
}
