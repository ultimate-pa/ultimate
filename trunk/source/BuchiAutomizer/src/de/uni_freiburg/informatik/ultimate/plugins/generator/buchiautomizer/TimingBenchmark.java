package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.BenchmarkData;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class TimingBenchmark implements ICsvProviderProvider<Double>{
	private BenchmarkData m_BenchmarkData;
	
	public TimingBenchmark(BuchiCegarLoopBenchmarkGenerator benchGen) {
		m_BenchmarkData = new BenchmarkData();
		m_BenchmarkData.aggregateBenchmarkData(benchGen);
	}

	@Override
	public String toString() {
		return m_BenchmarkData.toString();
	}

	@Override
	public ICsvProvider<Double> createCvsProvider() {
		ICsvProvider<Double> rtr = new SimpleCsvProvider<>(new ArrayList<String>());
		return rtr;
	}
}
