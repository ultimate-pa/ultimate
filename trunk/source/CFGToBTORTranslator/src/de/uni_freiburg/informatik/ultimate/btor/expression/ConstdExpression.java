package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public class ConstdExpression extends BtorExpression {

	private final long constant;

	public ConstdExpression(final BtorSort sort, final long constant) {
		super(sort);
		this.constant = constant;
	}

	public long getConstant() {
		return constant;
	}

	@Override
	public boolean equalFields(final BtorExpression other) {
		if (((ConstdExpression) other).constant == constant) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int hash = "constd".hashCode();
		return (int) (hash * constant);
	}

	@Override
	public int dumpExpression(final int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap) throws IOException {
		if (!assignnid(currentLine)) {
			return currentLine;
		}
		writer.write(String.valueOf(nid) + " constd " + String.valueOf(sortMap.get(sort)) + " "
				+ String.valueOf(constant) + "\n");
		writer.flush();
		return currentLine + 1;
	}

}
