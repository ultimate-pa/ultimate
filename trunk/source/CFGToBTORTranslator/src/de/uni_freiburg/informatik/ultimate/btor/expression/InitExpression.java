package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;
import de.uni_freiburg.informatik.ultimate.btor.MaxDepthException;

public class InitExpression extends BtorExpression {

	private final StateExpression state;
	private final BtorExpression initVal;

	public InitExpression(final StateExpression state, final BtorExpression initVal) {
		super(state.sort);
		this.state = state;
		this.initVal = initVal;
	}

	@Override
	public boolean equalFields(final BtorExpression other) {
		if ((((InitExpression) other).state == state) && (((InitExpression) other).initVal == initVal)) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int hash = "init".hashCode();
		return hash * state.hashCode() * System.identityHashCode(initVal);
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
		currentLine = initVal.dumpExpression(currentLine, writer, sortMap, maxDepth - 1);
		currentLine = state.dumpExpression(currentLine, writer, sortMap, maxDepth - 1);

		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " init " + String.valueOf(sortMap.get(sort)) + " "
				+ String.valueOf(state.nid) + " " + String.valueOf(initVal.nid) + "\n");
		writer.flush();
		return currentLine + 1;
	}
}