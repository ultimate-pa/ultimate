package de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex;

public class RegexToTgf<L> implements IRegexVisitor<L> {

	protected int mNextNodeId = 0;
	protected final StringBuilder mNodeList = new StringBuilder();
	protected final StringBuilder mEdgeList = new StringBuilder();

	protected int addNode(final String label) {
		mNodeList.append(mNextNodeId).append(' ').append(label).append('\n');
		return mNextNodeId++;
	}
	
	protected void addEdge(final int sourceId, final int targetId) {
		mEdgeList.append(sourceId).append(' ').append(targetId).append('\n');
	}
	
	public void visit(final Union<L> union) {
		final int thisId = addNode("∪");
		addEdge(thisId, mNextNodeId);
		union.getFirst().accept(this);
		addEdge(thisId, mNextNodeId);
		union.getSecond().accept(this);
	}

	public void visit(final Concatenation<L> concatenation) {
		final int thisId = addNode("·");
		addEdge(thisId, mNextNodeId);
		concatenation.getFirst().accept(this);
		addEdge(thisId, mNextNodeId);
		concatenation.getSecond().accept(this);
	}

	public void visit(final Star<L> star) {
		final int thisId = addNode("*");
		addEdge(thisId, mNextNodeId);
		star.getInner().accept(this);
	}

	public void visit(final Literal<L> literal) {
		addNode(literal.getLetter().toString());
	}

	public void visit(final Epsilon<L> epsilon) {
		addNode("ε");
	}

	public void visit(final EmptySet<L> emptySet) {
		addNode("∅");
	}

	public String toString() {
		return mNodeList + "#\n" + mEdgeList;
	}

}
