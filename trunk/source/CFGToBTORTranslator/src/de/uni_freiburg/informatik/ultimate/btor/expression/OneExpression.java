package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;
import de.uni_freiburg.informatik.ultimate.btor.MaxDepthException;

public class OneExpression extends BtorExpression {

	public OneExpression(final BtorSort sort) {
		super(sort);
	}

	@Override
	public boolean equalFields(final BtorExpression other) {
		return true;
	}

	@Override
	public int hashCode() {
		final int hash = "one".hashCode();
		return hash;
	}

	@Override
	public int dumpExpression(final int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap, int maxDepth) throws IOException, MaxDepthException {
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " one " + String.valueOf(sortMap.get(sort)) + "\n");
		writer.flush();
		return currentLine + 1;
	}
}
