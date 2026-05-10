package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public abstract class BinaryExpression extends BtorExpression {

	private final BtorExpression left;
	private final BtorExpression right;

	public BinaryExpression(final BtorSort sort, final BtorExpression left, final BtorExpression right) {
		super(sort);
		this.left = left;
		this.right = right;
	}

	public abstract String name();

	@Override
	public boolean equalFields(final BtorExpression other) {
		if ((((BinaryExpression) other).left == left) && (((BinaryExpression) other).right == right)) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int hash = name().hashCode();
		return hash * left.hashCode() * right.hashCode();
	}

	@Override
	public int dumpExpression(int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap) throws IOException {
		currentLine = left.dumpExpression(currentLine, writer, sortMap);
		currentLine = right.dumpExpression(currentLine, writer, sortMap);
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " " + name() + " " + String.valueOf(sortMap.get(sort)) + " "
				+ String.valueOf(left.nid) + " " + String.valueOf(right.nid) + "\n");
		return currentLine + 1;
	}

}
