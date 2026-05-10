package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class StateExpression extends BtorExpression {

	private final String name;

	public StateExpression(final BtorSort sort, final String name) {
		super(sort);
		this.name = name;
	}

	@Override
	public boolean equalFields(final BtorExpression other) {
		if (((StateExpression) other).name == name) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int hash = "state".hashCode();
		return hash * name.hashCode();
	}

	@Override
	public int dumpExpression(final int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap) throws IOException {
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " state " + String.valueOf(sortMap.get(sort)) + " " + name + "\n");
		writer.flush();
		return currentLine + 1;
	}
}
