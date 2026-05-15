package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class InitExpression extends BtorExpression {

	private final StateExpression state;
	private final BtorExpression initVal;

	public InitExpression(final StateExpression state, final BtorExpression initVal) {
		super(state.sort);
		this.state = state;
		this.initVal = initVal;
	}

	@Override
	public boolean equalFields(final BtorExpression other) {
		if ((((InitExpression) other).state == state) && (((InitExpression) other).initVal == initVal)) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int hash = "init".hashCode();
		return hash * state.hashCode() * initVal.hashCode();
	}

	@Override
	public int dumpExpression(int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap) throws IOException {
		currentLine = initVal.dumpExpression(currentLine, writer, sortMap);
		currentLine = state.dumpExpression(currentLine, writer, sortMap);

		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " init " + String.valueOf(sortMap.get(sort)) + " "
				+ String.valueOf(state.nid) + " " + String.valueOf(initVal.nid) + "\n");
		writer.flush();
		return currentLine + 1;
	}
}