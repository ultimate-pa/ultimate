/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CountertraceParser plug-in.
 *
 * The ULTIMATE CountertraceParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CountertraceParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CountertraceParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CountertraceParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CountertraceParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.countertrace.parser;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;

/**
 * Result of parsing a single countertrace line from a {@code .ct} file.
 *
 * <p>
 * Each line may optionally start with an ID followed by a colon (e.g., {@code ID001: ⌈R⌉;true}), analogous to the
 * {@code .req} file format. If no ID is present, {@link #getId()} returns {@code null}.
 * </p>
 *
 * @author University of Freiburg
 */
public class CountertraceParserResult {

	private final String mId;
	private final CounterTrace mCounterTrace;

	public CountertraceParserResult(final String id, final CounterTrace counterTrace) {
		mId = id;
		mCounterTrace = Objects.requireNonNull(counterTrace);
	}

	/**
	 * @return The ID of this countertrace, or {@code null} if no ID was specified.
	 */
	public String getId() {
		return mId;
	}

	/**
	 * @return The parsed {@link CounterTrace}.
	 */
	public CounterTrace getCounterTrace() {
		return mCounterTrace;
	}

	@Override
	public String toString() {
		if (mId == null) {
			return mCounterTrace.toString();
		}
		return mId + ": " + mCounterTrace.toString();
	}
}
