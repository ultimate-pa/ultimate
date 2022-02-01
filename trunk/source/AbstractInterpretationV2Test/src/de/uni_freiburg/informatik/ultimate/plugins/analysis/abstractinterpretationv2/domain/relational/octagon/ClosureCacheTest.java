package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

public class ClosureCacheTest {

	public static void main(String[] args) {
		int fails = 0;
		int tests = 0;

		final OctMatrix[] testCases = new OctMatrix[500000];

		// put manual test cases here
		
		for (int i = 0; i < testCases.length; ++i) {
			OctMatrix m = testCases[i];
			if (m == null) {
				m = OctMatrix.random(3);
			}
			m = m.cachedTightClosure(); // build up cache
			if (m.hasNegativeSelfLoop()) {
				continue;
			}
			
			// closure-updating operation under test
			m.cachedTightClosure().negateVar(0);
			
			final OctMatrix updatedCachedClosure = m.cachedTightClosure();
			final OctMatrix newlyComputedClosure = m.tightClosure(OctMatrix::shortestPathClosurePrimitiveSparse);
			if (!updatedCachedClosure.isEqualTo(newlyComputedClosure)) {
				System.out.println("CLOSURES DIFFER");
				System.out.println(updatedCachedClosure);
				System.out.println(newlyComputedClosure);
				++fails;
			}
			++tests;
		}
		System.out.println();
		System.out.println("FAILS: " + fails + " / " + tests);
	}
	
}
