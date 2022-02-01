/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant;

import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * 
 * Wrapper for {@link TracePredicates} together with their origin and their quality, i.e., if they are perfect or not.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class QualifiedTracePredicates {
	private final TracePredicates mTracePredicates;
	private final boolean mIsPerfect;
	private final Class<?> mOrigin;

	public QualifiedTracePredicates(final TracePredicates sequence, final Class<?> origin, final boolean isPerfect) {
		mTracePredicates = Objects.requireNonNull(sequence);
		mOrigin = Objects.requireNonNull(origin);
		mIsPerfect = isPerfect;
	}

	public boolean isPerfect() {
		return mIsPerfect;
	}

	public TracePredicates getTracePredicates() {
		return mTracePredicates;
	}

	public Class<?> getOrigin() {
		return mOrigin;
	}

	public List<IPredicate> getPredicates() {
		return mTracePredicates.getPredicates();
	}

	public static List<TracePredicates> toList(final List<QualifiedTracePredicates> usedIpps) {
		if (usedIpps.isEmpty()) {
			return Collections.emptyList();
		}
		return usedIpps.stream().map(QualifiedTracePredicates::getTracePredicates).collect(Collectors.toList());
	}

	@Override
	public String toString() {
		return mTracePredicates.toString();
	}
}