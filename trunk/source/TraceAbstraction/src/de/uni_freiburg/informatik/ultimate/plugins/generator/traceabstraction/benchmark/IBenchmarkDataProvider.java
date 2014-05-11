package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark;

/**
 * Classes that implement this interface can provide data to our benchmarks.
 * Our benchmarks are key-value stores.
 * @author Matthias Heizmann
 *
 */
public interface IBenchmarkDataProvider {

	public abstract Iterable<String> getKeys();
	
	public abstract Object getValue(String key);
	
	public abstract IBenchmarkType getBenchmarkType();

}