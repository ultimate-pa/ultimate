package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

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

	private final Map<ACTION, Summary> mSummaries;
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
	 * @param hierachicalPreState
	 * @param postState
	 * @param current
	 *            An action that leaves a scope
	 */
	void addSummary(final AbstractMultiState<STATE, ACTION, VARDECL> hierachicalPreState,
			final AbstractMultiState<STATE, ACTION, VARDECL> postState, final ACTION current) {
		// current is a call, but we have to find the summary
		final ACTION summaryAction = getSummaryAction(current);
		final Summary oldSummary = mSummaries.get(summaryAction);
		final Summary newSummary;
		if (oldSummary != null && hierachicalPreState.isSubsetOf(oldSummary.getPreState()) != SubsetResult.NONE) {
			newSummary = getMergedSummary(oldSummary, hierachicalPreState, postState);
		} else {
			newSummary = new Summary(hierachicalPreState, postState);
		}
		mSummaries.put(summaryAction, newSummary);
		logCurrentSummaries(current);
	}

	private void logCurrentSummaries(final ACTION current) {
		if (!mLogger.isDebugEnabled()) {
			return;
		}
		final ACTION summaryAction = getSummaryAction(current);
		final Summary summary = mSummaries.get(summaryAction);
		if (summary == null) {
			return;
		}
		mLogger.debug(AbsIntPrefInitializer.INDENT + " Current summaries for "
				+ LoggingHelper.getTransitionString(current, mTransProvider) + ":");
		mLogger.debug(AbsIntPrefInitializer.DINDENT + " PreCall " + LoggingHelper.getStateString(summary.getPreState())
				+ " PostCall " + LoggingHelper.getStateString(summary.getPostState()));
	}

	private ACTION getSummaryAction(final ACTION current) {
		final Collection<ACTION> succActions = mTransProvider.getSuccessorActions(mTransProvider.getSource(current));
		return succActions.stream().filter(a -> mTransProvider.isSummaryForCall(a, current)).findAny()
				.orElseThrow(AssertionError::new);
	}

	AbstractMultiState<STATE, ACTION, VARDECL> getSummaryPostState(final ACTION current,
			final AbstractMultiState<STATE, ACTION, VARDECL> preCallState) {
		final Summary summary = mSummaries.get(current);
		if (summary == null) {
			return null;
		}
		if (preCallState.isSubsetOf(summary.getPreState()) != SubsetResult.NONE) {
			return summary.getPostState();
		}
		return null;
	}

	private Summary getMergedSummary(final Summary summary,
			final AbstractMultiState<STATE, ACTION, VARDECL> hierachicalPreState,
			final AbstractMultiState<STATE, ACTION, VARDECL> postState) {
		final AbstractMultiState<STATE, ACTION, VARDECL> newPre =
				summary.getPreState().merge(mMergeOp, hierachicalPreState);
		final AbstractMultiState<STATE, ACTION, VARDECL> newPost = summary.getPostState().merge(mMergeOp, postState);
		return new Summary(newPre, newPost);
	}

	@Override
	public String toString() {
		return mSummaries.toString();
	}

	/**
	 * Container for scope stack items.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	private final class Summary {
		private final AbstractMultiState<STATE, ACTION, VARDECL> mPreState;
		private final AbstractMultiState<STATE, ACTION, VARDECL> mPostState;

		private Summary(final AbstractMultiState<STATE, ACTION, VARDECL> preState,
				final AbstractMultiState<STATE, ACTION, VARDECL> postState) {
			mPreState = preState;
			mPostState = postState;
		}

		AbstractMultiState<STATE, ACTION, VARDECL> getPostState() {
			return mPostState;
		}

		AbstractMultiState<STATE, ACTION, VARDECL> getPreState() {
			return mPreState;
		}
	}
}
