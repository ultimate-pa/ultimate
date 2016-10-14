package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
final class SummaryMap<STATE extends IAbstractState<STATE, ACTION, VARDECL>, ACTION, VARDECL, LOCATION> {

	private final Map<String, Set<Summary>> mSummaries;
	private final IAbstractStateBinaryOperator<STATE> mMergeOp;
	private final ITransitionProvider<ACTION, LOCATION> mTransProvider;
	private final ILogger mLogger;

	SummaryMap(final IAbstractStateBinaryOperator<STATE> mergeOp, final ITransitionProvider<ACTION, LOCATION> trans,
			final ILogger logger) {
		mTransProvider = trans;
		mMergeOp = mergeOp;
		mSummaries = new HashMap<>();
		mLogger = logger;
	}

	/**
	 *
	 * @param callPostState
	 * @param returnPreState
	 * @param callStatement
	 *            An action that leaves a scope
	 */
	void addSummary(final AbstractMultiState<STATE, ACTION, VARDECL> callPostState,
			final AbstractMultiState<STATE, ACTION, VARDECL> returnPreState, final ACTION callStatement) {
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
			final AbstractMultiState<STATE, ACTION, VARDECL> callPostState,
			final AbstractMultiState<STATE, ACTION, VARDECL> returnPreState, final ACTION callStatement) {
		final Iterator<Summary> iter = oldSummaries.iterator();
		final Summary rtr;
		while (iter.hasNext()) {
			final Summary current = iter.next();
			final AbstractMultiState<STATE, ACTION, VARDECL> currentPre = current.getCallPostState();
			final AbstractMultiState<STATE, ACTION, VARDECL> currentPost = current.getReturnPreState();
			if (callPostState.isSubsetOf(currentPre) != SubsetResult.NONE) {
				final AbstractMultiState<STATE, ACTION, VARDECL> newCallPost =
						currentPre.merge(mMergeOp, callPostState);
				final AbstractMultiState<STATE, ACTION, VARDECL> newReturnPre =
						currentPost.merge(mMergeOp, returnPreState);
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

	AbstractMultiState<STATE, ACTION, VARDECL> getSummaryPostState(final ACTION summaryAction,
			final AbstractMultiState<STATE, ACTION, VARDECL> preCallState) {
		final String procName = mTransProvider.getProcedureName(summaryAction);
		final Set<Summary> summary = getSummary(procName);
		return summary.stream().filter(a -> preCallState.isSubsetOf(a.getCallPostState()) != SubsetResult.NONE)
				.findAny().map(a -> a.getReturnPreState()).orElse(null);
	}

	private final Set<Summary> getSummary(final String procName) {
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
		private final AbstractMultiState<STATE, ACTION, VARDECL> mCallPostState;
		private final AbstractMultiState<STATE, ACTION, VARDECL> mReturnPreState;

		private Summary(final AbstractMultiState<STATE, ACTION, VARDECL> callPost,
				final AbstractMultiState<STATE, ACTION, VARDECL> returnPre) {
			mCallPostState = callPost;
			mReturnPreState = returnPre;
		}

		AbstractMultiState<STATE, ACTION, VARDECL> getReturnPreState() {
			return mReturnPreState;
		}

		AbstractMultiState<STATE, ACTION, VARDECL> getCallPostState() {
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
