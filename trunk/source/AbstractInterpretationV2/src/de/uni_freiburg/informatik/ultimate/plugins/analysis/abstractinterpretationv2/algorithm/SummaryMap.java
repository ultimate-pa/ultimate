/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
final class SummaryMap<STATE extends IAbstractState<STATE>, ACTION, LOCATION>
		implements ISummaryStorage<STATE, ACTION, LOCATION> {

	private final Map<String, Set<Summary>> mSummaries;
	private final ITransitionProvider<ACTION, LOCATION> mTransProvider;
	private final ILogger mLogger;

	SummaryMap(final ITransitionProvider<ACTION, LOCATION> trans, final ILogger logger) {
		mTransProvider = trans;
		mSummaries = new HashMap<>();
		mLogger = logger;
	}

	@Override
	public DisjunctiveAbstractState<STATE> getSummaryPostState(final ACTION summaryAction,
			final DisjunctiveAbstractState<STATE> preCallState) {
		final String procName = mTransProvider.getProcedureName(summaryAction);
		final Set<Summary> summary = getSummary(procName);
		final DisjunctiveAbstractState<STATE> rtr =
				summary.stream().filter(a -> preCallState.isSubsetOf(a.getCallPostState()) != SubsetResult.NONE)
						.findAny().map(a -> a.getReturnPreState()).orElse(null);
		return rtr;
	}

	/**
	 *
	 * @param callPostState
	 * @param returnPreState
	 * @param callStatement
	 *            An action that leaves a scope
	 */
	void addSummary(final DisjunctiveAbstractState<STATE> callPostState,
			final DisjunctiveAbstractState<STATE> returnPreState, final ACTION callStatement) {
		// current is a call, but we have to find the summary
		final String procName = mTransProvider.getProcedureName(callStatement);
		final Set<Summary> oldSummaries = getSummary(procName);

		final Summary newSummary;
		if (oldSummaries.isEmpty()) {
			newSummary = new Summary(callPostState, returnPreState);
			logCurrentSummaries("Adding first summary", callStatement, newSummary);
		} else {
			newSummary = updateSummaries(oldSummaries, callPostState, returnPreState, callStatement);
		}
		oldSummaries.add(newSummary);
	}

	private Summary updateSummaries(final Set<Summary> oldSummaries,
			final DisjunctiveAbstractState<STATE> callPostState, final DisjunctiveAbstractState<STATE> returnPreState,
			final ACTION callStatement) {
		final Iterator<Summary> iter = oldSummaries.iterator();
		final Summary rtr;
		while (iter.hasNext()) {
			final Summary current = iter.next();
			final DisjunctiveAbstractState<STATE> currentPre = current.getCallPostState();
			final DisjunctiveAbstractState<STATE> currentPost = current.getReturnPreState();
			if (callPostState.isSubsetOf(currentPre) != SubsetResult.NONE) {
				final DisjunctiveAbstractState<STATE> newCallPost = currentPre.union(callPostState);
				final DisjunctiveAbstractState<STATE> newReturnPre = currentPost.union(returnPreState);
				iter.remove();
				rtr = new Summary(newCallPost, newReturnPre);
				logCurrentSummaries("Del summary", callStatement, current);
				logCurrentSummaries("Add summary", callStatement, rtr);
				return rtr;
			}
		}
		rtr = new Summary(callPostState, returnPreState);
		logCurrentSummaries("Add summary", callStatement, rtr);
		return rtr;
	}

	private void logCurrentSummaries(final String message, final ACTION current, final Summary newSummary) {
		if (!mLogger.isDebugEnabled()) {
			return;
		}
		assert newSummary != null;
		mLogger.debug(AbsIntPrefInitializer.DINDENT + " " + message + " " + LoggingHelper.getHashCodeString(current)
				+ ": PreCall " + LoggingHelper.getStateString(newSummary.getCallPostState()) + " PreReturn "
				+ LoggingHelper.getStateString(newSummary.getReturnPreState()));
	}

	private Set<Summary> getSummary(final String procName) {
		final Set<Summary> summaries = mSummaries.get(procName);
		if (summaries == null) {
			final HashSet<Summary> freshSummaries = new HashSet<>();
			mSummaries.put(procName, freshSummaries);
			return freshSummaries;
		}
		return summaries;
	}

	@Override
	public String toString() {
		return mSummaries.toString();
	}

	/**
	 * Container a procedure summary, consisting of state after call and state before return
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	private final class Summary {
		private final DisjunctiveAbstractState<STATE> mCallPostState;
		private final DisjunctiveAbstractState<STATE> mReturnPreState;

		private Summary(final DisjunctiveAbstractState<STATE> callPost,
				final DisjunctiveAbstractState<STATE> returnPre) {
			mCallPostState = callPost;
			mReturnPreState = returnPre;
		}

		DisjunctiveAbstractState<STATE> getReturnPreState() {
			return mReturnPreState;
		}

		DisjunctiveAbstractState<STATE> getCallPostState() {
			return mCallPostState;
		}

		@Override
		public String toString() {
			return "{CallPost: " + LoggingHelper.getStateString(mCallPostState) + " ReturnPre: "
					+ LoggingHelper.getStateString(mReturnPreState) + "}";
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((mReturnPreState == null) ? 0 : mReturnPreState.hashCode());
			result = prime * result + ((mCallPostState == null) ? 0 : mCallPostState.hashCode());
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			@SuppressWarnings("unchecked")
			final Summary other = (Summary) obj;
			if (mReturnPreState == null) {
				if (other.mReturnPreState != null) {
					return false;
				}
			} else if (!mReturnPreState.equals(other.mReturnPreState)) {
				return false;
			}
			if (mCallPostState == null) {
				if (other.mCallPostState != null) {
					return false;
				}
			} else if (!mCallPostState.equals(other.mCallPostState)) {
				return false;
			}
			return true;
		}
	}
}
