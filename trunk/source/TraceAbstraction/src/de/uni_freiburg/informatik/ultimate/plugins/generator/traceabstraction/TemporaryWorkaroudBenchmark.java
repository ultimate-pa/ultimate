package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

public class TemporaryWorkaroudBenchmark implements ICsvProviderProvider<Double> {
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
	@Override
	public ICsvProvider<Double> createCvsProvider() {
		return m_TraceAbstractionBenchmarks.createCvsProvider();
	}
	
	

}
