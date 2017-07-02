/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorAutomatonStatisticsGenerator.EnhancementType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorTraceContainer.ErrorTrace;

/**
 * Container for one or more error traces.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type in the trace
 */
public class ErrorTraceContainer<LETTER> implements Iterable<ErrorTrace<LETTER>> {
	private final List<ErrorTrace<LETTER>> mTraces = new LinkedList<>();

	/**
	 * @param trace
	 *            Error trace.
	 * @param precondition
	 *            precondition
	 */
	public void addTrace(final IRun<LETTER, IPredicate, ?> trace, final IPredicate precondition) {
		mTraces.add(new ErrorTrace<>(trace, precondition));
	}

	/**
	 * @param trace
	 *            Error trace.
	 */
	public void addTrace(final IRun<LETTER, IPredicate, ?> trace) {
		addTrace(trace, null);
	}

	/**
	 * @param precondition
	 *            Error precondition (may also be {@code null}).
	 */
	public void addPrecondition(final IPredicate precondition) {
		if (precondition != null) {
			mTraces.get(mTraces.size() - 1).mPrecondition = precondition;
		}
	}

	/**
	 * TODO remove this and the field after collecting statistics.
	 * @param enhancement Enhancement type.
	 */
	public void addEnhancementType(final EnhancementType enhancement) {
		mTraces.get(mTraces.size() - 1).mEnhancement = enhancement;
	}

	/**
	 * @return {@code true} iff there is no error trace.
	 */
	public boolean isEmpty() {
		return mTraces.isEmpty();
	}

	/**
	 * @return Number of error traces stored.
	 */
	public int size() {
		return mTraces.size();
	}

	@Override
	public Iterator<ErrorTrace<LETTER>> iterator() {
		return mTraces.iterator();
	}

	/**
	 * Wrapper for a single error trace.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @param <LETTER>
	 *            letter type in the trace
	 */
	public static final class ErrorTrace<LETTER> {
		private final IRun<LETTER, IPredicate, ?> mTrace;
		private IPredicate mPrecondition;
		public EnhancementType mEnhancement;

		/**
		 * @param trace
		 *            Error trace.
		 * @param precondition
		 *            precondition
		 */
		public ErrorTrace(final IRun<LETTER, IPredicate, ?> trace, final IPredicate precondition) {
			mTrace = trace;
			mPrecondition = precondition;
			mEnhancement = EnhancementType.UNKNOWN;
		}

		/**
		 * @param trace
		 *            Error trace.
		 */
		public ErrorTrace(final IRun<LETTER, IPredicate, ?> trace) {
			this(trace, null);
		}

		public IRun<LETTER, IPredicate, ?> getTrace() {
			return mTrace;
		}

		public IPredicate getPrecondition() {
			return mPrecondition;
		}

		public EnhancementType getEnhancement() {
			return mEnhancement;
		}
	}
}
