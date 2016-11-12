package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil;

/**
 * Represents an uninterpreted predicate symbol that appears in a set of Horn clauses.
 * This class is the node class for the Horn clause graph.
 * @author nutz, mostafa-mahmoud
 *
 */
public class HornClausePredicateSymbol {

	private int arity;
	private String name;
	
	public HornClausePredicateSymbol(String name, int arity) {
		this.name = name;
		this.arity = arity;
	}
	
	public String getName() {
		return name;
	}
	
	public int getArity() {
		return arity;
	}
	@Override
	public String toString() {
		return name;
	}
	
	public static class HornClauseFalsePredicateSymbol extends HornClausePredicateSymbol {
		public HornClauseFalsePredicateSymbol() {
			super("false", 0);
		}
	}
	
	public static class HornClauseTruePredicateSymbol  extends HornClausePredicateSymbol {
		public HornClauseTruePredicateSymbol() {
			super("true", 0);
		}
	}
}
