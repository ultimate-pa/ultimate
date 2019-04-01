package de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex;

public interface IRegexVisitor<L> {

	default void visit(final Union<L> union) {
		union.getFirst().accept(this);
		union.getSecond().accept(this);
	}

	default void visit(final Concatenation<L> concatenation) {
		concatenation.getFirst().accept(this);
		concatenation.getSecond().accept(this);
	}

	default void visit(final Star<L> star) {
		star.getInner().accept(this);
	}

	default void visit(final Literal<L> literal) {
		// base case, terminate
	}

	default void visit(final Epsilon<L> epsilon) {
		// base case, terminate
	}

	default void visit(final EmptySet<L> emptySet) {
		// base case, terminate
	}

}
