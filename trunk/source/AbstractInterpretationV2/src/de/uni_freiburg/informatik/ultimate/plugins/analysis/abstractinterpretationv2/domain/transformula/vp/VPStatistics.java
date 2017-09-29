package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.function.BinaryOperator;

public enum VPStatistics {
	MAX_WEQGRAPH_SIZE, MAX_SIZEOF_WEQEDGELABEL;


	public static BinaryOperator<Integer> getAggregator(final VPStatistics vps) {
		switch (vps) {
		case MAX_WEQGRAPH_SIZE:
			return Math::max;
		case MAX_SIZEOF_WEQEDGELABEL:
			return Math::max;
		default :
			throw new UnsupportedOperationException();
		}
	}

	public static Integer getInitialValue(final VPStatistics vps) {
		switch (vps) {
		case MAX_WEQGRAPH_SIZE:
			return 0;
		case MAX_SIZEOF_WEQEDGELABEL:
			return 0;
		default :
			throw new UnsupportedOperationException();
		}
	}
}
