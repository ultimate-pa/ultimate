/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

import java.util.function.BinaryOperator;

public enum VPStatistics {
	MAX_WEQGRAPH_SIZE, MAX_SIZEOF_WEQEDGELABEL, NO_SUPPORTING_EQUALITIES, NO_SUPPORTING_DISEQUALITIES, NO_DISJUNCTIONS,
	 MAX_NO_DISJUNCTIONS;


	public static BinaryOperator<Integer> getAggregator(final VPStatistics vps) {
		switch (vps) {
		case MAX_WEQGRAPH_SIZE:
		case MAX_SIZEOF_WEQEDGELABEL:
		case MAX_NO_DISJUNCTIONS:
			return Math::max;
		case NO_SUPPORTING_EQUALITIES:
		case NO_SUPPORTING_DISEQUALITIES:
		case NO_DISJUNCTIONS:
			return (i1, i2) -> i1 + i2;
		default :
			throw new UnsupportedOperationException();
		}
	}

	public static Integer getInitialValue(final VPStatistics vps) {
		switch (vps) {
		case MAX_WEQGRAPH_SIZE:
		case MAX_SIZEOF_WEQEDGELABEL:
		case MAX_NO_DISJUNCTIONS:
			return -1;
		case NO_SUPPORTING_EQUALITIES:
		case NO_SUPPORTING_DISEQUALITIES:
		case NO_DISJUNCTIONS:
			return 0;
		default :
			throw new UnsupportedOperationException();
		}
	}

	/**
	 * No all stats of this enum apply for every object. In these cases, they should return the values from here.
	 *
	 * @param stat
	 * @return a value for stat that makes it easy to notice if we are actually using it.
	 */
	public static Integer getNonApplicableValue(final VPStatistics stat) {
		switch (stat) {
		case MAX_WEQGRAPH_SIZE:
		case MAX_SIZEOF_WEQEDGELABEL:
		case MAX_NO_DISJUNCTIONS:
			return -2;
		case NO_SUPPORTING_EQUALITIES:
		case NO_SUPPORTING_DISEQUALITIES:
		case NO_DISJUNCTIONS:
			return -2;
		default :
			throw new UnsupportedOperationException();
		}
	}
}
