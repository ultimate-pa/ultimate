package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.BenchmarkData;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

public class TraceAbstractionBenchmarks implements ICsvProviderProvider<Object> {

	private final BenchmarkData m_CegarLoopBenchmarkData;
	private final int m_Locations;
	private final int m_ErrorLocations;

	public TraceAbstractionBenchmarks(RootAnnot rootAnnot) {
		m_Locations = rootAnnot.getNumberOfProgramPoints();
		m_ErrorLocations = rootAnnot.getNumberOfErrorNodes();
		m_CegarLoopBenchmarkData = new BenchmarkData();
	}

	public void aggregateBenchmarkData(CegarLoopBenchmarkGenerator cegarLoopBenchmarkGenerator) {
		m_CegarLoopBenchmarkData.aggregateBenchmarkData(cegarLoopBenchmarkGenerator);
	}

	public static String prettyprintNanoseconds(long time) {
		long seconds = time / 1000000000;
		long tenthDigit = (time / 100000000) % 10;
		return seconds + "." + tenthDigit + "s";
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("CFG has ");
		sb.append(m_Locations);
		sb.append(" locations, ");
		sb.append(m_ErrorLocations);
		sb.append(" error locations. ");
		sb.append(m_CegarLoopBenchmarkData.toString());
		return sb.toString();
	}

	@Override
	public ICsvProvider<Object> createCvsProvider() {
		return m_CegarLoopBenchmarkData.createCvsProvider();
	}

}
