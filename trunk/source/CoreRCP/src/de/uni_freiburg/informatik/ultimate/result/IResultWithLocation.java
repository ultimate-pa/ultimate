package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * IResult that is related to a location.
 * @author heizmann@informatik.uni-freiburg.de
 */
public interface IResultWithLocation extends IResult {
	/**
	 * Location of the input to which this result is related.
	 */
	public ILocation getLocation();
}
