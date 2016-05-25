
package jdd.util.jre;

import java.util.Arrays;
import java.util.Random;

import jdd.util.JDDConsole;
import jdd.util.math.FastRandom;


/**
 * <pre>
 * this files times some operations and checks if JRE implementation
 * faster the straight forward java code
 * </pre>
 */
public class JRETest {

	public static long memstart;

	public static void memstart() {
		for(int i = 0; i < 6; i++) {
			System.gc();
		}
		memstart = JREInfo.usedMemory();
	}

	public static long memend() {
		return JREInfo.usedMemory() - memstart;
	}

	public static int rnd_size(int i) {
		if(i < 0) {
			return 0;
		}
		final int x = (1 <<i);
		return x + (int)(Math.random() * x);
	}
	// -------------------------------------------------------
	public static void set1(int []x, int val) {
		final int len = x.length;
		for(int i = 0; i < len; i++) {
			x[i] = val;
		}
	}

	public static void set2(int []x, int val) {
		Arrays.fill(x, val);
	}

	public static void set3(int []x, int val) {
		int size = x.length / 4, o = 0;
		for(int i = 0; i < size; i++) {
			x[o] = val;
			x[o+1] = val;
			x[o+2] = val;
			x[o+3] = val;
			o += 4;
		}

		size = x.length & 3;
		while( size-- != 0) {
			x[o++] = val;
		}
	}

	// -------------------------------------------------------
	public static void copy1(int []x, int []y) {
		final int len = x.length;
		for(int i = 0; i < len; i++) {
			x[i] = y[i];
		}
	}

	public static void copy2(int []x, int []y) {
		System.arraycopy(y, 0, x, 0, x.length);
	}

	public static void copy3(int []x, int []y) {
		int size = x.length / 4, o = 0;
		for(int i = 0; i < size; i++) {
			x[o] = y[o];
			x[o+1] = y[o+1];
			x[o+2] = y[o+2];
			x[o+3] = y[o+3];
			o += 4;
		}

		size = x.length & 3;
		while( size-- != 0) {
			x[o] = y[o];
			o++;
		}

	}

	// -------------------------------------------------------
	public static void main(String args[]) {
		JREInfo.show();

		final JRETest test = new JRETest();

		final int SIZE = 10240;
		final int ROUNDS = 10240;
		final int [] buffer1 = new int[SIZE];
		final int [] buffer2 = new int[SIZE];


		// TEST SET CODE
		long tmp, code, lib;

		for(int i = 0; i < ROUNDS; i++)
		 {
			set1(buffer1, i);	// warmup:
		}

		tmp = System.currentTimeMillis();
		for(int i = 0; i < ROUNDS; i++) {
			set1(buffer1, i);
		}
		code = System.currentTimeMillis() - tmp;


		for(int i = 0; i < ROUNDS; i++)
		 {
			set2(buffer1, i);	// warmup:
		}
		tmp = System.currentTimeMillis();
		for(int i = 0; i < ROUNDS; i++) {
			set2(buffer1, i);
		}
		lib = System.currentTimeMillis() - tmp;

		if(code < lib) {
			System.out.println("SET: Java code is faster than Arrays.fill() [" +code + " vs " + lib + "]");
		} else {
			System.out.println("SET: Arrays.fill() is faster than Java code [" +lib + " vs " + code + "]");
		}


		for(int i = 0; i < ROUNDS; i++)
		 {
			set3(buffer1, i);	// warmup:
		}
		tmp = System.currentTimeMillis();
		for(int i = 0; i < ROUNDS; i++) {
			set3(buffer1, i);
		}
		code = System.currentTimeMillis() - tmp;

		if(code < lib) {
			System.out.println("SET: unrolled java code is faster than Arrays.fill() [" +code + " vs " + lib + "]");
		} else {
			System.out.println("SET: Arrays.fill() is faster than unrolled java code [" +lib + " vs " + code + "]");
		}


		// TEST COPY CODE
		for(int i = 0; i < ROUNDS; i++)
		 {
			copy1(buffer1, buffer2);	// warmup:
		}

		tmp = System.currentTimeMillis();
		for(int i = 0; i < ROUNDS; i++) {
			copy1(buffer1, buffer2);
		}
		code = System.currentTimeMillis() - tmp;


		for(int i = 0; i < ROUNDS; i++)
		 {
			copy2(buffer1, buffer2);	// warmup:
		}
		tmp = System.currentTimeMillis();
		for(int i = 0; i < ROUNDS; i++) {
			copy2(buffer1, buffer2);
		}
		lib = System.currentTimeMillis() - tmp;

		if(code < lib) {
			System.out.println("COPY: Java code is faster than System.arraycopy() [" +code + " vs " + lib + "]");
		} else {
			System.out.println("COPY: System.arraycopy() is faster than Java code [" +lib + " vs " + code + "]");
		}

		for(int i = 0; i < ROUNDS; i++)
		 {
			copy3(buffer1, buffer2);	// warmup:
		}
		tmp = System.currentTimeMillis();
		for(int i = 0; i < ROUNDS; i++) {
			copy3(buffer1, buffer2);
		}
		code = System.currentTimeMillis() - tmp;

		if(code < lib) {
			System.out.println("COPY: unrolled loop is faster than System.arraycopy() [" +code + " vs " + lib + "]");
		} else {
			System.out.println("COPY: System.arraycopy() is faster than unrolled loop [" +lib + " vs " + code + "]");
		}

		// memory test:
		memstart();
		final Object obj = new Object();
		final long obj_size = memend();
		System.out.println("MEMORY: Object size = " + obj_size);

		// PRNG speed test:
		int y; // we just need some number
		final int MAX = 10000;
		final Random rnd = new Random();
		long t1 = System.currentTimeMillis();
		for(int i = 0; i < 1000000; i++) {
			y = FastRandom.mtrand() % MAX;  y = FastRandom.mtrand() % MAX;
			y = FastRandom.mtrand() % MAX; y = FastRandom.mtrand() % MAX;
			y = FastRandom.mtrand() % MAX; y = FastRandom.mtrand() % MAX;
		}
		t1 = System.currentTimeMillis() - t1;


		long t2 = System.currentTimeMillis();
		for(int i = 0; i < 1000000; i++) {
			y = rnd.nextInt(MAX);	y = rnd.nextInt(MAX);	y = rnd.nextInt(MAX);
			y = rnd.nextInt(MAX);	y = rnd.nextInt(MAX);	y = rnd.nextInt(MAX);
		}
		t2 = System.currentTimeMillis() - t2;
		if(t1 < t2) {
			JDDConsole.out.println("LPRNG: FastRandom.mtrand() is " + ( 100 * t2 / t1 - 100) + "% faster that Java code");
		} else {
			JDDConsole.out.println("LPRNG: Java is " + ( 100 * t1 / t2 - 100) + "% faster that FastRandom.mtrand()");
		}


	}
}
