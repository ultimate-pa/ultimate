package de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.graph;

/**
 * Represents an uninterpreted predicate symbol that appears in a set of Horn clauses.
 * This class is the node class for the Horn clause graph.
 * @author nutz
 *
 */
public class HornClausePredicateSymbol {

	int arity;

	String name;
	
	
	public class HornClauseFalsePredicateSymbol extends HornClausePredicateSymbol {
		
	}
}
