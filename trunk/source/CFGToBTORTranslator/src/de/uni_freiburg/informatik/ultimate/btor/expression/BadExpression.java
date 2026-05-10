package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class BadExpression extends BtorExpression {

	BtorExpression bad;

	public BadExpression(final BtorExpression bad) {
		super(new BtorSort(0));
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
		return hash * bad.hashCode();
	}

	@Override
	public int dumpExpression(int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap) throws IOException {
		currentLine = bad.dumpExpression(currentLine, writer, sortMap);
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " bad " + String.valueOf(bad.nid) + "\n");
		writer.flush();
		return currentLine + 1;
	}
}
