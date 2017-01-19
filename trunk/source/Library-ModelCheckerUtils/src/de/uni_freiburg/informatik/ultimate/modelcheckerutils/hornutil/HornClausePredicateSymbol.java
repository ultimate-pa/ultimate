package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil;

/**
 * Represents an uninterpreted predicate symbol that appears in a set of Horn clauses. This class is the node class for
 * the Horn clause graph.
 * 
 * @author nutz, mostafa-mahmoud
 *
 */
public class HornClausePredicateSymbol {

	private final int mArity;
	private final String mName;

	public HornClausePredicateSymbol(final String name, final int arity) {
		mName = name;
		mArity = arity;
	}

	public String getName() {
		return mName;
	}

	public int getArity() {
		return mArity;
	}

	@Override
	public String toString() {
		return mName;
	}

	public static class HornClauseFalsePredicateSymbol extends HornClausePredicateSymbol {
		public HornClauseFalsePredicateSymbol() {
			super("false", 0);
		}
	}

	public static class HornClauseTruePredicateSymbol extends HornClausePredicateSymbol {
		public HornClauseTruePredicateSymbol() {
			super("true", 0);
		}
	}

	public static class HornClauseDontCareSymbol extends HornClausePredicateSymbol {
		public HornClauseDontCareSymbol() {
			super("€", 0);
		}
	}
}
