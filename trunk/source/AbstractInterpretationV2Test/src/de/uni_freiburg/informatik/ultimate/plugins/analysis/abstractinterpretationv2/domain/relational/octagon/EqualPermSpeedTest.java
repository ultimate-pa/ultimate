package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

public class EqualPermSpeedTest {

	public static void main(String[] args) {
		final int vars = 12;
		final int cycles = 10000000;
		
		final int[] map = new int[vars];
		for (int i = 0; i < vars; ++i) {
			map[i] = i;
		}

		long t1 = 0;
		long t2 = 0;
		for (int i = 0; i < cycles; ++i) {
			final OctMatrix a = OctMatrix.random(vars);
			final OctMatrix b = a.copy();
			long t;

			t = System.nanoTime();
			a.isEqualTo(b);
			t1 += System.nanoTime() - t;
			
			t = System.nanoTime();
			a.isEqualTo(b, map);
			t2 += System.nanoTime() - t;
		}
		final String format = "%15s: %8.2fs%n";
		System.out.format(format + format, "direct", t1*1e-9, "permutation", t2*1e-9);
		
		// result: isEqualToPermutation takes approx. 4.8 times longer (without creation of mapping)!
	}
	
}
