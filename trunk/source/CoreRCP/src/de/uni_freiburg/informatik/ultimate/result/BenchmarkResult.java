package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 * Result that should be used to report benchmark informations like (e.g.,
 * runtime, number of iterations, size of automata, size of predicates, ...).
 * These benchmark informations are stored in the m_Benchmark object. The
 * toString() method of this object has to return the benchmark results in human
 * readable form.
 * 
 * @author Matthias Heizmann
 * @param <T>
 */
public class BenchmarkResult<T> extends AbstractResult {

	private final String m_ShortDescrption;
	private final ICsvProviderProvider<T> m_Benchmark;

	public BenchmarkResult(String plugin, String shortDescrption, ICsvProviderProvider<T> m_Benchmark) {
		super(plugin);
		this.m_ShortDescrption = shortDescrption;
		this.m_Benchmark = m_Benchmark;
	}

	@Override
	public String getShortDescription() {
		return m_ShortDescrption;
	}

	@Override
	public String getLongDescription() {
		return m_Benchmark.toString();
	}

	public ICsvProviderProvider<T> getBenchmark() {
		return m_Benchmark;
	}

}
