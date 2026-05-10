package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

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
		return hash * child.hashCode();
	}

	@Override
	public int dumpExpression(int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap) throws IOException {
		currentLine = child.dumpExpression(currentLine, writer, sortMap);
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(
				String.valueOf(nid) + " " + name() + " " + String.valueOf(sortMap.get(sort)) + " " + child.nid + "\n");
		return currentLine + 1;
	}

}
