package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.BenchmarkData;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

public class BuchiAutomizerTimingBenchmark implements ICsvProviderProvider<Object>{
	private BenchmarkData m_BenchmarkData;
	
	public BuchiAutomizerTimingBenchmark(BuchiCegarLoopBenchmarkGenerator benchGen) {
		m_BenchmarkData = new BenchmarkData();
		m_BenchmarkData.aggregateBenchmarkData(benchGen);
	}

	@Override
	public String toString() {
		return m_BenchmarkData.toString();
	}

	@Override
	public ICsvProvider<Object> createCvsProvider() {
		return m_BenchmarkData.createCvsProvider();
	}
}
