package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;

public class IterationInfo {
	public static Info sizeInfo = new Info();

	public static class Info {
		public Integer mIteration = null;
		public String mInterpolantAutomaton = null;
		public String mAbstraction = null;
		public CegarLoopStatisticsGenerator mBenchmark = null;
	}

	public static Info newInstance() {
		return new Info();
	};
}
