package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
final class SummaryMap<STATE extends IAbstractState<STATE, ACTION, VARDECL>, ACTION, VARDECL, LOCATION> {

	private final Map<ACTION, Pair<AbstractMultiState<STATE, ACTION, VARDECL>, AbstractMultiState<STATE, ACTION, VARDECL>>> mSummaries;
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
		final Pair<AbstractMultiState<STATE, ACTION, VARDECL>, AbstractMultiState<STATE, ACTION, VARDECL>> oldSummary =
				mSummaries.get(summaryAction);
		final Pair<AbstractMultiState<STATE, ACTION, VARDECL>, AbstractMultiState<STATE, ACTION, VARDECL>> newSummary;
		if (oldSummary != null && hierachicalPreState.isSubsetOf(oldSummary.getFirst()) != SubsetResult.NONE) {
			newSummary = getMergedSummary(oldSummary, hierachicalPreState, postState);
		} else {
			newSummary = new Pair<>(hierachicalPreState, postState);
		}
		mSummaries.put(summaryAction, newSummary);
		logCurrentSummaries(current);
	}

	private void logCurrentSummaries(final ACTION current) {
		if (!mLogger.isDebugEnabled()) {
			return;
		}
		final ACTION summaryAction = getSummaryAction(current);
		final Pair<AbstractMultiState<STATE, ACTION, VARDECL>, AbstractMultiState<STATE, ACTION, VARDECL>> summary =
				mSummaries.get(summaryAction);
		if (summary == null) {
			return;
		}
		mLogger.debug(AbsIntPrefInitializer.INDENT + " Current summaries for "
				+ LoggingHelper.getTransitionString(current, mTransProvider) + ":");
		mLogger.debug(AbsIntPrefInitializer.DINDENT + " PreCall " + LoggingHelper.getStateString(summary.getFirst())
				+ " PostCall " + LoggingHelper.getStateString(summary.getSecond()));
	}

	private ACTION getSummaryAction(final ACTION current) {
		final Collection<ACTION> succActions = mTransProvider.getSuccessorActions(mTransProvider.getSource(current));
		return succActions.stream().filter(a -> mTransProvider.isSummaryForCall(a, current)).findAny().get();
	}

	AbstractMultiState<STATE, ACTION, VARDECL> getSummaryPostState(final ACTION current,
			final AbstractMultiState<STATE, ACTION, VARDECL> preCallState) {
		final Pair<AbstractMultiState<STATE, ACTION, VARDECL>, AbstractMultiState<STATE, ACTION, VARDECL>> summary =
				mSummaries.get(current);
		if (summary == null) {
			return null;
		}
		if (preCallState.isSubsetOf(summary.getFirst()) != SubsetResult.NONE) {
			return summary.getSecond();
		}
		return null;
	}

	private Pair<AbstractMultiState<STATE, ACTION, VARDECL>, AbstractMultiState<STATE, ACTION, VARDECL>>
			getMergedSummary(
					final Pair<AbstractMultiState<STATE, ACTION, VARDECL>, AbstractMultiState<STATE, ACTION, VARDECL>> summary,
					final AbstractMultiState<STATE, ACTION, VARDECL> hierachicalPreState,
					final AbstractMultiState<STATE, ACTION, VARDECL> postState) {
		final AbstractMultiState<STATE, ACTION, VARDECL> newPre =
				summary.getFirst().merge(mMergeOp, hierachicalPreState);
		final AbstractMultiState<STATE, ACTION, VARDECL> newPost = summary.getSecond().merge(mMergeOp, postState);
		return new Pair<>(newPre, newPost);
	}

	@Override
	public String toString() {
		return mSummaries.toString();
	}
}
