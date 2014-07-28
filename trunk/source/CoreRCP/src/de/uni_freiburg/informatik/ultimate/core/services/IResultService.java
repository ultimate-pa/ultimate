package de.uni_freiburg.informatik.ultimate.core.services;

import java.util.HashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.result.IResult;

public interface IResultService {

	public abstract HashMap<String, List<IResult>> getResults();

	public abstract void reportResult(String id, IResult result);

}