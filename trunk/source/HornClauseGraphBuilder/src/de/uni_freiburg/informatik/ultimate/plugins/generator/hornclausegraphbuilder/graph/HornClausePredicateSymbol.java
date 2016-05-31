package de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.graph;

/**
 * Represents an uninterpreted predicate symbol that appears in a set of Horn clauses.
 * This class is the node class for the Horn clause graph.
 * @author nutz, mostafa-mahmoud
 *
 */
public class HornClausePredicateSymbol {

	int arity;

	String name;
	
	public HornClausePredicateSymbol(String name, int arity) {
		this.name = name;
		this.arity = arity;
	}
	
	public String toString() {
		return name;
	}
	
	public static class HornClauseFalsePredicateSymbol extends HornClausePredicateSymbol {

		public HornClauseFalsePredicateSymbol() {
			super("false", 0);
		}
	}
}
