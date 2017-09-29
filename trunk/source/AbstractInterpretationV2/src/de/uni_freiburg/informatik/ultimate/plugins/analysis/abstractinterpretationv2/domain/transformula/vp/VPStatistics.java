package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.function.BinaryOperator;

public enum VPStatistics {
	MAX_WEQGRAPH_SIZE, MAX_SIZEOF_WEQEDGELABEL, NO_SUPPORTING_EQUALITIES, NO_SUPPORTING_DISEQUALITIES;


	public static BinaryOperator<Integer> getAggregator(final VPStatistics vps) {
		switch (vps) {
		case MAX_WEQGRAPH_SIZE:
		case MAX_SIZEOF_WEQEDGELABEL:
			return Math::max;
		case NO_SUPPORTING_EQUALITIES:
		case NO_SUPPORTING_DISEQUALITIES:
			return (i1, i2) -> i1 + i2;
		default :
			throw new UnsupportedOperationException();
		}
	}

	public static Integer getInitialValue(final VPStatistics vps) {
		switch (vps) {
		case MAX_WEQGRAPH_SIZE:
		case MAX_SIZEOF_WEQEDGELABEL:
		case NO_SUPPORTING_EQUALITIES:
		case NO_SUPPORTING_DISEQUALITIES:
			return 0;
		default :
			throw new UnsupportedOperationException();
		}
	}
}
