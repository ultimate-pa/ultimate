package de.uni_freiburg.informatik.ultimate.core.services;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.result.IResult;

/**
 * {@link IResultService} allows tools to report results.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public interface IResultService {

	/**
	 * @return A map containing all results of a toolchain up to now.
	 */
	Map<String, List<IResult>> getResults();

	/**
	 * Report a result to the Ultimate result service. The result may not be
	 * null and may not contain null values (i.e. at least
	 * {@link IResult#getShortDescription()} and
	 * {@link IResult#getLongDescription()} must not be null).
	 * 
	 * @param pluginId
	 *            The plugin ID of the tool which generated the result.
	 * @param result
	 *            The result itself.
	 */
	void reportResult(String pluginId, IResult result);
}
