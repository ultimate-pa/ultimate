package de.uni_freiburg.informatik.ultimate.btorutils;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;
import java.util.List;

public class BtorExpression {
	private final int sort;
	private final BtorExpressionType type;
	private final List<BtorExpression> children;
	private int nid;

	public BtorExpression(final int sort, final BtorExpressionType type, final List<BtorExpression> children) {
		this.sort = sort;
		this.type = type;
		this.children = children;
	}

	public int getSort() {
		return sort;
	}

	public BtorExpressionType getType() {
		return type;
	}

	public List<BtorExpression> getChildren() {
		return children;
	}

	public void assignnid(final int nid) {
		if (this.nid != 0) {
			throw new UnsupportedOperationException("nid already set");
		}
		this.nid = nid;
	}

	public int dumpExpression(int currentLine, final OutputStreamWriter writer, final HashMap<Integer, Integer> sortMap)
			throws IOException {
		if (children.isEmpty()) {
			assignnid(currentLine);
			writer.write(String.valueOf(nid) + " " + type.name().toLowerCase() + " " + String.valueOf(sortMap.get(sort))
					+ "\n");
		} else {
			for (final BtorExpression child : children) {
				currentLine = child.dumpExpression(currentLine, writer, sortMap);
			}
			assignnid(currentLine);
			writer.write(
					String.valueOf(nid) + " " + type.name().toLowerCase() + " " + String.valueOf(sortMap.get(sort)));
			for (final BtorExpression child : children) {
				writer.write(" " + String.valueOf(child.nid));
			}
			writer.write("\n");
		}
		writer.flush();
		currentLine++;
		return currentLine;
	}
}
