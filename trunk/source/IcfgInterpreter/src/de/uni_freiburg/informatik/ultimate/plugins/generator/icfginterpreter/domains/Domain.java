package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm.ReturnType;

public interface Domain<T extends Domain<T>> {
	/** Create a Domain that includes all values of this and the given domain */
	T union(T domain);

	/** Create a Domain that includes all values that are in both this and the given domain */
	T intersection(T domain);

	/** Create a Domain that includes all values that are in either but not both domains */
	T difference(T domain);

	/** Create a Domain that includes all values that are in this domain but not the other */
	default T complement(final T domain) {
		return difference(intersection(domain));
	}

	/** Test if all values of the given domain are in this domain */
	boolean contains(Domain<?> domain);

	boolean isEmpty();

	ArrayList<? extends Object> getValues();

	ReturnType getType();

	T getFullDomain();

	/** Domain created from an int, bool, bitvector, or SMTArray */
	T domainFrom(Object singleValue);

	@Override
	boolean equals(Object b);

	@Override
	String toString();
}
