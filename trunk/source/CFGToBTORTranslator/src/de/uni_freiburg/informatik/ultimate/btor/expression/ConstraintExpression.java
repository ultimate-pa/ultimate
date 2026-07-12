package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;
import de.uni_freiburg.informatik.ultimate.btor.MaxDepthException;

public class ConstraintExpression extends BtorExpression {

	BtorExpression constraint;

	public ConstraintExpression(final BtorExpression constraint) {
		super(new BtorSort(1));
		this.constraint = constraint;
	}

	@Override
	public boolean equalFields(final BtorExpression other) {
		if (((ConstraintExpression) other).constraint == constraint) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int hash = "constraint".hashCode();
		return hash * constraint.hashCode();
	}

	@Override
	public int dumpExpression(int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap, int maxDepth) throws IOException, MaxDepthException {
		currentLine = constraint.dumpExpression(currentLine, writer, sortMap, maxDepth - 1);
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " constraint " + String.valueOf(constraint.nid) + "\n");
		writer.flush();
		return currentLine + 1;
	}
}
