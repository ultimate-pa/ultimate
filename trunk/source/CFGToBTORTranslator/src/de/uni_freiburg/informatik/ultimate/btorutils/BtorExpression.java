package de.uni_freiburg.informatik.ultimate.btorutils;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public class BtorExpression {
	private final int sort;
	private final BtorExpressionType type;
	private final List<BtorExpression> children;
	private final long constant;
	private int nid;

	public BtorExpression(final int sort, final BtorExpressionType type, final List<BtorExpression> children) {
		this.sort = sort;
		this.type = type;
		this.children = children;
		constant = 0;
	}

	public BtorExpression(final int sort, final long constant) {
		this.sort = sort;
		type = BtorExpressionType.CONSTD;
		children = new ArrayList<>();
		this.constant = constant;
	}

	public BtorExpression(final int sort, final BtorExpressionType type) {
		this.sort = sort;
		this.type = type;
		children = new ArrayList<>();
		constant = 0;
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

	public long getConstant() {
		return constant;
	}

	public boolean assignnid(final int nid) {
		if (this.nid != 0) {
			return false;
		}
		this.nid = nid;
		return true;
	}

	public int dumpExpression(int currentLine, final OutputStreamWriter writer, final HashMap<Integer, Integer> sortMap)
			throws IOException {
		if (children.isEmpty()) {
			if (!assignnid(currentLine)) {
				return currentLine;
			}
			if (type == BtorExpressionType.CONSTD) {
				writer.write(String.valueOf(nid) + " " + type.name().toLowerCase() + " "
						+ String.valueOf(sortMap.get(sort) + " " + String.valueOf(constant)) + "\n");
			} else {
				writer.write(String.valueOf(nid) + " " + type.name().toLowerCase() + " "
						+ String.valueOf(sortMap.get(sort)) + "\n");
			}
		} else {
			for (final BtorExpression child : children) {
				currentLine = child.dumpExpression(currentLine, writer, sortMap);
			}
			if (!assignnid(currentLine)) {
				return currentLine;
			}
			// handling for error locations
			if (type == BtorExpressionType.BAD) {
				writer.write(String.valueOf(nid) + " " + type.name().toLowerCase() + " "
						+ String.valueOf(children.get(0).nid));
			} else {
				writer.write(String.valueOf(nid) + " " + type.name().toLowerCase() + " "
						+ String.valueOf(sortMap.get(sort)));
				for (final BtorExpression child : children) {
					writer.write(" " + String.valueOf(child.nid));
				}
			}
			writer.write("\n");
		}
		writer.flush();
		currentLine++;
		return currentLine;
	}
}
