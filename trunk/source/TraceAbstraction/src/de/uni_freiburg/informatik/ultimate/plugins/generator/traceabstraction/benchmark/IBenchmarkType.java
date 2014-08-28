package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark;

import java.util.Collection;


/**
 * Classes that implement this interface define a type of benchmark that is a
 * key-value store. These classes define the following.
 * <li> the allows keys
 * <li> how several benchmark objects can be aggregated into one. Therefore
 * classes that implement this interface define how values of several objects 
 * have to be aggregated (e.g. taking the sum, or taking the maximum)
 * <li> how benchmark data can be prettyprinted 
 * @author Matthias Heizmann
 */
public interface IBenchmarkType {
	
	Collection<String> getKeys();
	
	Object aggregate(String key, Object value1, Object value2);

	String prettyprintBenchmarkData(IBenchmarkDataProvider benchmarkData);

}
