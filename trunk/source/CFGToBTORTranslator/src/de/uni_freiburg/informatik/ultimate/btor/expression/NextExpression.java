package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;
import de.uni_freiburg.informatik.ultimate.btor.MaxDepthException;

public class NextExpression extends BtorExpression {

	private final StateExpression state;
	private final BtorExpression nextVal;

	public NextExpression(final StateExpression state, final BtorExpression nextVal) {
		super(state.sort);
		this.state = state;
		this.nextVal = nextVal;
	}

	public BtorExpression getNextVal() {
		return nextVal;
	}

	@Override
	public boolean equalFields(final BtorExpression other) {
		if ((((NextExpression) other).state == state) && (((NextExpression) other).nextVal == nextVal)) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int hash = "next".hashCode();
		return hash * state.hashCode() * System.identityHashCode(nextVal);
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
		currentLine = state.dumpExpression(currentLine, writer, sortMap, maxDepth - 1);
		currentLine = nextVal.dumpExpression(currentLine, writer, sortMap, maxDepth - 1);
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " next " + String.valueOf(sortMap.get(sort)) + " "
				+ String.valueOf(state.nid) + " " + String.valueOf(nextVal.nid) + "\n");
		writer.flush();
		return currentLine + 1;
	}
}
