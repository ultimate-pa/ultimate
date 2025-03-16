package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm.ReturnType;

/** A constructor with no elements should create an empty domain. */
public interface Domain<T extends Domain<T>> {
	/** Create a Domain that includes all values of this and the given domain */
	T union(Domain<?> domain);

	/** Create a Domain that includes all values that are in both this and the given domain */
	T intersection(Domain<?> domain);

	/** Create a Domain that includes all values that are in either but not both domains */
	T difference(Domain<?> domain);

	/** Create a Domain that includes all values that are in this domain but not the other */
	default T complement(final Domain<?> domain) {
		return difference(intersection(domain));
	}

	/** Test if all values of the given domain are in this domain */
	boolean contains(Domain<?> domain);

	boolean isEmpty();

	/** Returns the number of possible values in the domain */
	long getValueCount();

	ArrayList<? extends Object> getValues();

	ReturnType getType();

	/** Return a domain of the same type as this that contains all possible values */
	T getFullDomain();

	/** Domain created from an int, bool, bitvector, or SMTArray */
	T domainFrom(Object singleValue);

	@Override
	boolean equals(Object b);

	@Override
	String toString();
}
