package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive;

public class IterationInfo {
	public static Info instance = new Info();

	public static Info newInstance() {
		return new Info();
	};

	public static class Info {
		public Integer mIteration = null;
		public String mInterpolantAutomaton = null;
		public String mAbstraction = null;

		public Info setIteration(final Integer iteration) {
			mIteration = iteration;
			return this;
		}
	}
}
