package de.uni_freiburg.informatik.ultimatetest.decider.overallResult;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.result.IResult;

/**
 * Classes that implement this interface can be used to evaluate an overall
 * result.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <OVERALL_RESULT> Type that we use to represent possible overall
 * results. Typically we use an enum type.
 */
public interface IOverallResultEvaluator<OVERALL_RESULT> {
	
	/**
	 * Use the IResults computed by Ultimate to evaluate an overall result.
	 * This method should compute the overall result and the most significant
	 * IResults such that both will be available using the getters below.
	 */
	public void evaluateOverallResult(IResultService resultService);
	
	/**
	 * Getter for overall result. Should be called only after the overall result
	 * was computed by the evaluateOverallResult(...) method.
	 */
	public OVERALL_RESULT getOverallResult();
	
	/**
	 * Returns a String that describes the overall result.
	 * This can be getOverallResult().toString(), but desirable is a more
	 * detailed description.
	 * 
	 */
	public String generateOverallResultMessage(); 
	
	/**
	 * Returns all IResults that are most significant while evaluating the
	 * overall result. E.g., if a safety checker reports some UNKNOWN IResults
	 * and some UNSAFE IResults, the UNSAFE IResults are more significant 
	 * because they determine that the overall result is UNSAFE
	 */
	public Set<IResult> getMostSignificantResults();

}
