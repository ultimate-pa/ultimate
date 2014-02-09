package de.uni_freiburg.informatik.ultimate.util;

import java.util.concurrent.TimeUnit;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.util.Benchmark;

/***
 * 
 * @author Dietsch
 * 
 */
public class BenchmarkTest {

	@BeforeClass
	public static void Setup() {

	}

	@Test
	public void TimeStartStopSingle() throws InterruptedException {

		long actualTime = 100;
		double measuredTime = -1;
		double allowedEpsilon = 1;
		String title = "Test";

		Benchmark bench = new Benchmark();

		bench.start(title);
		Thread.sleep(actualTime);
		bench.stop(title);

		measuredTime = bench.getElapsedTime(title, TimeUnit.MILLISECONDS);
		System.out.println("Measured time was " + measuredTime + "ms, and should be " + actualTime + "ms");
		System.out.println(bench.getReportString(title));
		
		Assert.assertTrue(Math.abs(actualTime - measuredTime) <= allowedEpsilon);
	}
	
	@Test
	public void HeapStartStopSingle() throws InterruptedException {

		int numInt = 1000000;
		int actualHeapSize=numInt*(Integer.SIZE/Byte.SIZE);
		
		long measuredHeapDelta = -1;
		double allowedEpsilon = 1;
		String title = "Test";

		Benchmark bench = new Benchmark();

		Thread.sleep(100);
		bench.start(title);
		int[] array = new int[numInt];
		for(int i=0;i<numInt;++i){
			array[i]=i;
		}
		Thread.sleep(100);
		bench.stop(title);

		long startSize  = bench.getStartHeapFreeSize(title);
		long stopSize  = bench.getStopHeapFreeSize(title);
		measuredHeapDelta = startSize-stopSize;
		
		System.out.println("Measured heap delta was " + measuredHeapDelta + " byte, and should be " + actualHeapSize + " byte");
		System.out.println(bench.getReportString(title));
		System.out.println("We print the array length to keep the array from being thrown away: "+array.length);
		
		Assert.assertTrue(Math.abs(actualHeapSize - measuredHeapDelta) <= allowedEpsilon);
	}

	@Test
	public void TimePauseSingle() throws InterruptedException {

		long actualTime = 100;
		double measuredTime = -1;
		double allowedEpsilon = 1;
		String title = "Test";

		Benchmark bench = new Benchmark();

		bench.start(title);
		Thread.sleep(actualTime);
		
		bench.pause(title);
		Thread.sleep(actualTime);
		bench.unpause(title);
		
		Thread.sleep(actualTime);
		
		bench.pause(title);
		Thread.sleep(actualTime);
		bench.unpause(title);
		
		Thread.sleep(actualTime);
		
		bench.stop(title);

		// we expect that we measured 3 Thread.sleep() periods instead of 5.
		actualTime = 3 * actualTime;

		measuredTime = bench.getElapsedTime(title, TimeUnit.MILLISECONDS);
		System.out.println("Measured time was " + measuredTime + "ms, and should be " + actualTime + "ms");
		System.out.println(bench.getReportString(title));

		Assert.assertTrue(Math.abs(actualTime - measuredTime) <= allowedEpsilon);
	}

}
