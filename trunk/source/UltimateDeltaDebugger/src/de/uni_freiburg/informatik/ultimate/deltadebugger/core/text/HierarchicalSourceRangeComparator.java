package de.uni_freiburg.informatik.ultimate.deltadebugger.core.text;

import java.util.Comparator;

/**
 * first offset comes first, larger range first on same offset
 */
public enum HierarchicalSourceRangeComparator implements Comparator<ISourceRange> {
	INSTANCE;

	public static HierarchicalSourceRangeComparator getInstance() {
		return INSTANCE;
	}

	@Override
	public int compare(final ISourceRange lhs, final ISourceRange rhs) {
		final int res = Integer.compare(lhs.offset(), rhs.offset());
		if (res == 0) {
			return Integer.compare(rhs.endOffset(), lhs.endOffset());
		}
		return res;
	}
}