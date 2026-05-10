package de.uni_freiburg.informatik.ultimate.btor.expression;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.btor.BtorSort;

public abstract class BtorExpression {
	protected final BtorSort sort;
	protected int nid;

	public BtorExpression(final BtorSort sort) {
		this.sort = sort;
		nid = 0; // initialize nid as unset
	}

	// assign node id to expression
	public boolean assignnid(final int nid) {
		if (this.nid != 0) {
			return false;
		}
		this.nid = nid;
		return true;
	}

	public BtorSort getSort() {
		return sort;
	}

	// write expression to output stream
	public abstract int dumpExpression(int currentLine, final OutputStreamWriter writer,
			final HashMap<BtorSort, Integer> sortMap) throws IOException;

	@Override
	public boolean equals(final Object other) {
		if (this == other) {
			return true;
		}
		if (other == null) {
			return false;
		}
		if (!(other instanceof BtorExpression)) {
			return false;
		}
		if (!sort.equals(((BtorExpression) other).sort)) {
			return false;
		}
		if (this.getClass() != other.getClass()) {
			return false;
		}

		return equalFields((BtorExpression) other);
	}

	// check for structural equality
	public abstract boolean equalFields(BtorExpression other);

	@Override
	public abstract int hashCode();

//	public Set<BtorSort> getRequiredBtorSorts() {
//		final Set<BtorSort> sorts = new HashSet<>();
//		sorts.add(sort);
//		if (!children.isEmpty()) {
//			for (final BtorExpression child : children) {
//				sorts.addAll(child.getRequiredBtorSorts());
//			}
//		}
//		return sorts;
//	}
//
//	public int dumpExpression(int currentLine, final OutputStreamWriter writer,
//			final HashMap<BtorSort, Integer> sortMap) throws IOException {
//		if (children.isEmpty()) {
//			if (!assignnid(currentLine)) {
//				return currentLine;
//			}
//			if (type == BtorExpressionType.CONSTD) {
//				writer.write(String.valueOf(nid) + " " + type.name().toLowerCase() + " "
//						+ String.valueOf(sortMap.get(sort)) + " " + String.valueOf(constant) + "\n");
//			} else if (type == BtorExpressionType.STATE || type == BtorExpressionType.INPUT) {
//				writer.write(String.valueOf(nid) + " " + type.name().toLowerCase() + " "
//						+ String.valueOf(sortMap.get(sort)) + " " + stateName + "\n");
//			} else if (type == BtorExpressionType.SEXT) {
//				writer.write(String.valueOf(nid) + " " + type.name().toLowerCase() + " "
//						+ String.valueOf(sortMap.get(sort)) + " " + String.valueOf(constant) + "\n");
//			} else {
//				writer.write(String.valueOf(nid) + " " + type.name().toLowerCase() + " "
//						+ String.valueOf(sortMap.get(sort)) + "\n");
//			}
//		} else {
//			for (final BtorExpression child : children) {
//				currentLine = child.dumpExpression(currentLine, writer, sortMap);
//			}
//			if (!assignnid(currentLine)) {
//				return currentLine;
//			}
//			// handling for error locations
//			if (type == BtorExpressionType.BAD || type == BtorExpressionType.CONSTRAINT) {
//				writer.write(String.valueOf(nid) + " " + type.name().toLowerCase() + " "
//						+ String.valueOf(children.get(0).nid));
//			} else {
//				writer.write(String.valueOf(nid) + " " + type.name().toLowerCase() + " "
//						+ String.valueOf(sortMap.get(sort)));
//				for (final BtorExpression child : children) {
//					writer.write(" " + String.valueOf(child.nid));
//				}
//			}
//			writer.write("\n");
//		}
//		writer.flush();
//		currentLine++;
//		return currentLine;
//	}
}
