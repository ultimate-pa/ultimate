package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.BenchmarkData;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class TimingBenchmark implements ICsvProviderProvider<Double>{
	private BenchmarkData m_BenchmarkData;
	
	public TimingBenchmark(BuchiCegarLoopBenchmarkGenerator benchGen) {
		m_BenchmarkData = new BenchmarkData(BuchiCegarLoopBenchmark.getInstance());
		m_BenchmarkData.aggregateBenchmarkData(benchGen);
	}

	@Override
	public String toString() {
		return m_BenchmarkData.toString();
	}

	@Override
	public ICsvProvider<Double> createCvsProvider() {
		SimpleCsvProvider<Double> rtr = new SimpleCsvProvider<>(new String[] { });

		return rtr;
	}
}
