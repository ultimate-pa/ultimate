package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;
import de.uni_freiburg.informatik.ultimate.btor.MaxDepthException;

public abstract class TernaryExpression extends BtorExpression {

	private final BtorExpression first;
	private final BtorExpression second;
	private final BtorExpression third;

	public TernaryExpression(final BtorSort sort, final BtorExpression first, final BtorExpression second,
			final BtorExpression third) {
		super(sort);
		this.first = first;
		this.second = second;
		this.third = third;
	}

	public abstract String name();

	public BtorExpression getThird() {
		return third;
	}

	@Override
	public boolean equalFields(final BtorExpression other) {
		if ((((TernaryExpression) other).first == first) && (((TernaryExpression) other).second == second)
				&& (((TernaryExpression) other).third == third)) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int hash = name().hashCode();
		return hash * System.identityHashCode(first) * System.identityHashCode(second) * System.identityHashCode(third);
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
		currentLine = first.dumpExpression(currentLine, writer, sortMap, maxDepth - 1);
		currentLine = second.dumpExpression(currentLine, writer, sortMap, maxDepth - 1);
		currentLine = third.dumpExpression(currentLine, writer, sortMap, maxDepth - 1);
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " " + name() + " " + String.valueOf(sortMap.get(sort)) + " "
				+ String.valueOf(first.nid) + " " + String.valueOf(second.nid) + " " + String.valueOf(third.nid)
				+ "\n");
		return currentLine + 1;
	}

}
