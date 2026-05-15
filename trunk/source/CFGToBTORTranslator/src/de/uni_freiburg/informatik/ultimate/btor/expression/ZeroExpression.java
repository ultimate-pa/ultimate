package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class ZeroExpression extends BtorExpression {

	public ZeroExpression(final BtorSort sort) {
		super(sort);
	}

	@Override
	public boolean equalFields(final BtorExpression other) {
		return true;
	}

	@Override
	public int hashCode() {
		final int hash = "zero".hashCode();
		return hash;
	}

	@Override
	public int dumpExpression(final int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap) throws IOException {
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " zero " + String.valueOf(sortMap.get(sort)) + "\n");
		writer.flush();
		return currentLine + 1;
	}
}
