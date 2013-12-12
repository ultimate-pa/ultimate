package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public interface IResultWithTrace extends IResult {

	
	public List<ILocation> getFailurePath();
}
