package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

public class TemporaryWorkaroudBenchmark {
	private final String m_OtherBenchmarkData;
	private final TraceAbstractionBenchmarks m_TraceAbstractionBenchmarks;
	public TemporaryWorkaroudBenchmark(String otherBenchmarkData,
			TraceAbstractionBenchmarks traceAbstractionBenchmarks) {
		super();
		m_OtherBenchmarkData = otherBenchmarkData;
		m_TraceAbstractionBenchmarks = traceAbstractionBenchmarks;
	}
	@Override
	public String toString() {
		return m_OtherBenchmarkData + " " + m_TraceAbstractionBenchmarks.printBenchmarkResults();
	}
	
	

}
