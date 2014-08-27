package de.uni_freiburg.informatik.ultimatetest.decider.overallResult;

import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.result.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.ITimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;


/**
 * Evaluate the overall result of a safety checker.
 * 
 * First, we iterate through all IResults returned by Ultimate and put them
 * into categories (which IResult is a witness for which overall result).
 * Afterwards we iterate through all categories in the order of their 
 * significance. The first non-empty category is our overall result.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class TerminationAnalysisOverallResultEvaluator implements IOverallResultEvaluator<TerminationAnalysisOverallResult> {
	
	private final HashRelation<TerminationAnalysisOverallResult, IResult> m_Category2Results = 
			new HashRelation<TerminationAnalysisOverallResult, IResult>();
	private TerminationAnalysisOverallResult m_OverallResult;
	private Set<IResult> m_MostSignificantResults;
	
	public void evaluateOverallResult(IResultService resultService) {
		for (Entry<String, List<IResult>> entry  : resultService.getResults().entrySet()) {
			for (IResult result  : entry.getValue()) {
				TerminationAnalysisOverallResult category = detectResultCategory(result);
				m_Category2Results.addPair(category, result);
			}
		}
		TerminationAnalysisOverallResult[] categoriesOrderedBySignificance = 
				new TerminationAnalysisOverallResult[] {
				TerminationAnalysisOverallResult.EXCEPTION_OR_ERROR,
				TerminationAnalysisOverallResult.SYNTAX_ERROR,
				TerminationAnalysisOverallResult.UNSUPPORTED_SYNTAX,
				TerminationAnalysisOverallResult.NONTERMINATING,
				TerminationAnalysisOverallResult.UNKNOWN,
				TerminationAnalysisOverallResult.TIMEOUT,
				TerminationAnalysisOverallResult.TERMINATING
		};
		
		for (TerminationAnalysisOverallResult category : categoriesOrderedBySignificance) {
			if (m_Category2Results.getDomain().contains(category)) {
				m_OverallResult = category;
			}
		}
		
		if (m_OverallResult == null) {
			m_OverallResult = TerminationAnalysisOverallResult.NO_RESULT;
		} else {
			m_MostSignificantResults = m_Category2Results.getImage(m_OverallResult);
		}
	}
	
	
	private TerminationAnalysisOverallResult detectResultCategory(IResult result) {
//		if (result instanceof AllSpecificationsHoldResult) {
//			return TerminationAnalysisOverallResult.SAFE;
//		} else if (result instanceof CounterExampleResult) {
//			return TerminationAnalysisOverallResult.UNSAFE;
//		} else if (result instanceof UnprovableResult) {
//			return TerminationAnalysisOverallResult.UNKNOWN;
//		} else if (result instanceof TypeErrorResult) {
//			return TerminationAnalysisOverallResult.SYNTAX_ERROR;
//		} else if (result instanceof SyntaxErrorResult) {
//			return TerminationAnalysisOverallResult.SYNTAX_ERROR;
//		} else if (result instanceof ITimeoutResult) {
//			return TerminationAnalysisOverallResult.TIMEOUT;
//		} else if (result instanceof UnsupportedSyntaxResult) {
//			return TerminationAnalysisOverallResult.UNSUPPORTED_SYNTAX;
//		} else if (result instanceof ExceptionOrErrorResult) {
//			return TerminationAnalysisOverallResult.EXCEPTION_OR_ERROR;
//		} else {
			return null;
//		}
	}


	@Override
	public TerminationAnalysisOverallResult getOverallResult() {
		return m_OverallResult;
	}
	
	@Override
	public String generateOverallResultMessage() {
		switch (getOverallResult()) {
		case EXCEPTION_OR_ERROR:
			return getMostSignificantResults().toString();
		case NO_RESULT:
			return getOverallResult().toString();
		case TERMINATING:
			return getMostSignificantResults().toString();
		case SYNTAX_ERROR:
			return getMostSignificantResults().toString();
		case TIMEOUT:
			return getMostSignificantResults().toString();
		case UNKNOWN:
			return concatenateShortDescriptions(getMostSignificantResults());
		case NONTERMINATING:
			return concatenateShortDescriptions(getMostSignificantResults());
		case UNSUPPORTED_SYNTAX:
			return getMostSignificantResults().toString();
		default:
			throw new AssertionError("unknown overall result");
		}
	}


	@Override
	public Set<IResult> getMostSignificantResults() {
		return m_MostSignificantResults;
	}
	
	
	private String concatenateShortDescriptions(Set<IResult> iresults) {
		StringBuilder sb = new StringBuilder();
		for (IResult iResult : iresults) {
			sb.append(iResult.getShortDescription());
			sb.append(" ");
		}
		return sb.toString();
	}



}
