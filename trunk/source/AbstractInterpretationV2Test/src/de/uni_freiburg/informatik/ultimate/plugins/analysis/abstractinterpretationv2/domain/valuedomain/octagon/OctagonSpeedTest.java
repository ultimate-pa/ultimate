package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.octagon;

import java.util.function.Consumer;

import org.junit.Assert;
import org.junit.Test;

public class OctagonSpeedTest {

	// -XX:+PrintCompilation -verbose:gc
	// -XX:-BackgroundCompilation
	public static void main(String[] args) {
		new OctagonSpeedTest(100).runAll();
		new OctagonSpeedTest(1000).runAll();
	}
	
	/** Number of variables (= matrix size / 2). */
	private final int mVars;
	private final int mWarmUpCycles = 1500;
	private final int mTestCycles = 1500;
	
	public OctagonSpeedTest(int size) {
		this.mVars = size;
	}
	
	public void runAll() {
		System.out.println("T E S T ############");
		System.out.println(mVars + " vars");
		System.out.println(mWarmUpCycles + " warm-up cycles");
		System.out.println(mTestCycles + " test cycles");
		System.out.println("get ----------------");
		runTest(this::testGet);
		System.out.println("set ----------------");
		runTest(this::testSet);
		System.out.println("elementwise --------");
		runTest(this::testElementwise);
		System.out.println();
	}
	
	public void runTest(Consumer<OctMatrix> test) {
		OctMatrix a = new OctMatrix(mVars);
		
		System.out.println("\twarm up ...");
		for (int i = 0; i < 1000; ++i)
			test.accept(a);
		
		System.out.println("\trun test ...");
		long time = System.nanoTime();
		for (int i = 0; i < 1000; ++i)
			test.accept(a);
		time = System.nanoTime() - time;
		System.out.printf("\ttest took %f s%n", time * 1e-9);
	}
	
	public void testGet(OctMatrix a) {
		int size = a.getSize();
		int sum = 0;
		for (int i = 0; i < size; ++i)
			for (int j = 0; j < size; ++j)
				a.get(i, j);
	}
	
	public void testSet(OctMatrix a) {
		int size = a.getSize();
		for (int i = 0; i < size; ++i) {
			for (int j = 0; j < size; ++j) {
				if (i == j)
					continue;
				a.set(i, j, OctValue.ZERO);				
			}
		}
	}

	public void testElementwise(OctMatrix a) {
		a.add(a).hashCode();
	}

}
