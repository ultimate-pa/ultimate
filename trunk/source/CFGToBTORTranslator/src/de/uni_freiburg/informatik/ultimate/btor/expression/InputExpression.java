package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;
import de.uni_freiburg.informatik.ultimate.btor.MaxDepthException;

public class InputExpression extends BtorExpression {

	private final String name;

	public InputExpression(final BtorSort sort, final String name) {
		super(sort);
		this.name = name;
	}

	@Override
	public boolean equalFields(final BtorExpression other) {
		if (((InputExpression) other).name.equals(name)) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int hash = "input".hashCode();
		return hash * name.hashCode();
	}

	@Override
	public int dumpExpression(final int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap, int maxDepth) throws IOException, MaxDepthException {
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " input " + String.valueOf(sortMap.get(sort)) + " " + name + "\n");
		writer.flush();
		return currentLine + 1;
	}
}
