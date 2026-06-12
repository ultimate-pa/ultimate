package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class SliceExpression extends BtorExpression {

	private final BtorExpression child;
	private final int upper;
	private final int lower;

	public SliceExpression(final BtorExpression child, final int upper, final int lower) {
		super(new BtorSort(upper - lower + 1));
		this.child = child;
		this.upper = upper;
		this.lower = lower;
	}

	@Override
	public boolean equalFields(final BtorExpression other) {
		if ((((SliceExpression) other).upper == upper) && (((SliceExpression) other).lower == lower)
				&& (((SliceExpression) other).child.equals(child))) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int hash = "slice".hashCode();
		return hash * upper * lower * child.hashCode();
	}

	@Override
	public int dumpExpression(int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap) throws IOException {
		currentLine = child.dumpExpression(currentLine, writer, sortMap);
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " slice " + String.valueOf(sortMap.get(sort)) + " " + child.nid + " " + upper
				+ " " + lower + "\n");
		writer.flush();
		return currentLine + 1;
	}
}