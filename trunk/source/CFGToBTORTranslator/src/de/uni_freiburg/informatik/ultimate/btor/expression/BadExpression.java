package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;
import de.uni_freiburg.informatik.ultimate.btor.MaxDepthException;

public class BadExpression extends BtorExpression {

	BtorExpression bad;

	public BadExpression(final BtorExpression bad) {
		super(new BtorSort(1));
		this.bad = bad;
	}

	@Override
	public boolean equalFields(final BtorExpression other) {
		if (((BadExpression) other).bad == bad) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int hash = "bad".hashCode();
		return hash * System.identityHashCode(bad);
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
		currentLine = bad.dumpExpression(currentLine, writer, sortMap, maxDepth - 1);
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " bad " + String.valueOf(bad.nid) + "\n");
		writer.flush();
		return currentLine + 1;
	}
}
