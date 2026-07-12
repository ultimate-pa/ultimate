package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;
import de.uni_freiburg.informatik.ultimate.btor.MaxDepthException;

public abstract class UnaryExpression extends BtorExpression {

	private final BtorExpression child;

	public UnaryExpression(final BtorSort sort, final BtorExpression child) {
		super(sort);
		this.child = child;
	}

	public abstract String name();

	@Override
	public boolean equalFields(final BtorExpression other) {
		if (((UnaryExpression) other).child == child) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int hash = name().hashCode();
		return hash * System.identityHashCode(child);
	}

	@Override
	public int dumpExpression(int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap, final int maxDepth) throws IOException, MaxDepthException {
		if (maxDepth == 0 && nid == 0) {
			throw new MaxDepthException(currentLine);
		}
		if (nid != 0) {
			return currentLine;
		}
		currentLine = child.dumpExpression(currentLine, writer, sortMap, maxDepth - 1);
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(
				String.valueOf(nid) + " " + name() + " " + String.valueOf(sortMap.get(sort)) + " " + child.nid + "\n");
		return currentLine + 1;
	}

}
