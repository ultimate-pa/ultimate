package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class SextExpression extends BtorExpression {

	private final BtorExpression child;
	private final int extendBy;

	public SextExpression(final BtorExpression child, final int extendBy) {
		super(new BtorSort(child.sort.size + extendBy));
		this.child = child;
		this.extendBy = extendBy;
	}

	@Override
	public boolean equalFields(final BtorExpression other) {
		if ((((SextExpression) other).extendBy == extendBy) && (((SextExpression) other).child.equals(child))) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int hash = "sext".hashCode();
		return hash * extendBy * child.hashCode();
	}

	@Override
	public int dumpExpression(int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap) throws IOException {
		currentLine = child.dumpExpression(currentLine, writer, sortMap);
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " sext " + String.valueOf(sortMap.get(sort)) + " " + child.nid + " "
				+ extendBy + "\n");
		writer.flush();
		return currentLine + 1;
	}
}