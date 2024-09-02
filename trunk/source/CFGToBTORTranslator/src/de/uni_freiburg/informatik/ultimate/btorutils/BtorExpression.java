package de.uni_freiburg.informatik.ultimate.btorutils;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public class BtorExpression {
	private final BtorSort sort;
	private final BtorExpressionType type;
	private final List<BtorExpression> children;
	private final long constant;
	private final String stateName;
	private int nid;
	public static HashMap allExpressions;

	public BtorExpression(final BtorSort sort, final BtorExpressionType type, final List<BtorExpression> children) {
		this.sort = sort;
		this.type = type;
		this.children = children;
		constant = 0;
		stateName = "";
	}

	public BtorExpression(final BtorSort sort, final long constant) {
		this.sort = sort;
		type = BtorExpressionType.CONSTD;
		children = new ArrayList<>();
		this.constant = constant;
		stateName = "";
	}

	public BtorExpression(final BtorSort sort, final BtorExpressionType type) {
		this.sort = sort;
		this.type = type;
		children = new ArrayList<>();
		constant = 0;
		stateName = "";
	}

	public BtorExpression(final BtorSort sort, final String name) {
		this.sort = sort;
		type = BtorExpressionType.STATE;
		children = new ArrayList<>();
		constant = 0;
		stateName = name;
	}

	public BtorSort getSort() {
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

	public static boolean addExpression(final BtorSort sort, final BtorExpressionType type,
			final List<BtorExpression> children) {
		final BtorExpression newExpression = new BtorExpression(sort, type, children);
		if (allExpressions.containsKey(newExpression)) {
			return true;
		}
		allExpressions.put(newExpression, newExpression);
		return false;
	}

	public static boolean addExpression(final BtorSort sort, final long constant) {
		final BtorExpression newExpression = new BtorExpression(sort, constant);
		if (allExpressions.containsKey(newExpression)) {
			return true;
		}
		allExpressions.put(newExpression, newExpression);
		return false;
	}

	public static boolean addExpression(final BtorSort sort, final BtorExpressionType type) {
		final BtorExpression newExpression = new BtorExpression(sort, type);
		if (allExpressions.containsKey(newExpression)) {
			return true;
		}
		allExpressions.put(newExpression, newExpression);
		return false;
	}

	public static boolean addExpression(final BtorSort sort, final String name) {
		final BtorExpression newExpression = new BtorExpression(sort, name);
		if (allExpressions.containsKey(newExpression)) {
			return true;
		}
		allExpressions.put(newExpression, newExpression);
		return false;
	}

	public boolean assignnid(final int nid) {
		if (this.nid != 0) {
			return false;
		}
		this.nid = nid;
		return true;
	}

	public int dumpExpression(int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap) throws IOException {
		if (children.isEmpty()) {
			if (!assignnid(currentLine)) {
				return currentLine;
			}
			if (type == BtorExpressionType.CONSTD) {
				writer.write(String.valueOf(nid) + " " + type.name().toLowerCase() + " "
						+ String.valueOf(sortMap.get(sort)) + " " + String.valueOf(constant) + "\n");
			} else if (type == BtorExpressionType.STATE) {
				writer.write(String.valueOf(nid) + " " + type.name().toLowerCase() + " "
						+ String.valueOf(sortMap.get(sort)) + " " + stateName + "\n");
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
