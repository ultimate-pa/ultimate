package de.uni_freiburg.informatik.ultimate.test.decider.overallresult;

import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TreeAutomizerSatResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TreeAutomizerUnsatResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;

public class TreeAutomizerOverallResultEvaluator implements IOverallResultEvaluator<TreeAutomizerOverallResult> {

	private TreeAutomizerOverallResult mOverallResult;
	private final Set<IResult> mMostSignificatResults = new HashSet<>();

	@Override
	public void evaluateOverallResult(IResultService resultService) {
		TreeAutomizerSatResult satResult = null;
		TreeAutomizerUnsatResult unsatResult = null;
		TimeoutResult timeoutResult = null;
		for (Entry<String, List<IResult>> en : resultService.getResults().entrySet()) {
			for (IResult res : en.getValue()) {
				if (res instanceof TreeAutomizerSatResult) {
					assert satResult == null && unsatResult == null : "more than one (un)sat result";
					satResult = (TreeAutomizerSatResult) res;
					mMostSignificatResults.add(res);
				} else if (res instanceof TreeAutomizerUnsatResult) {
					assert satResult == null && unsatResult == null : "more than one (un)sat result";
					unsatResult = (TreeAutomizerUnsatResult) res;
					mMostSignificatResults.add(res);
				} else if (res instanceof TimeoutResult) {
					timeoutResult = (TimeoutResult) res;
					mMostSignificatResults.add(res);
				}
			}
		}
		
		if (satResult != null) {
			mOverallResult = TreeAutomizerOverallResult.SAT;
		} else if (unsatResult != null) {
			mOverallResult = TreeAutomizerOverallResult.UNSAT;
		} else if (timeoutResult != null) {
			mOverallResult = TreeAutomizerOverallResult.TIMEOUT;
		} else {
			mOverallResult = TreeAutomizerOverallResult.UNKNOWN;
		}
	}

	@Override
	public TreeAutomizerOverallResult getOverallResult() {
		assert mOverallResult != null;
		return mOverallResult;
	}

	@Override
	public String generateOverallResultMessage() {
		return "most significant results: " + mMostSignificatResults;
	}

	@Override
	public Set<IResult> getMostSignificantResults() {
		return mMostSignificatResults;
	}

}
