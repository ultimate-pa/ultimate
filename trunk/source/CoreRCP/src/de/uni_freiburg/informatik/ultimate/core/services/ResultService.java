package de.uni_freiburg.informatik.ultimate.core.services;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.IResultWithLocation;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class ResultService implements IStorable, IResultService {

	private final HashMap<String, List<IResult>> mResults;
	private static final String sKey = "ResultService";

	private ResultService() {
		mResults = new HashMap<>();
	}

	@Override
	public void destroy() {
		mResults.clear();
	}

	@Override
	public Map<String, List<IResult>> getResults() {
		return mResults;
	}

	@Override
	public void reportResult(String id, IResult result) {
		if (result instanceof IResultWithLocation) {
			if (((IResultWithLocation) result).getLocation() == null) {
				throw new IllegalArgumentException("Location is null");
			}
		}
		if (result.getShortDescription() == null) {
			throw new IllegalArgumentException("ShortDescription is null");
		}
		if (result.getLongDescription() == null) {
			throw new IllegalArgumentException("LongDescription is null");
		}
		List<IResult> list = mResults.get(id);
		if (list == null) {
			list = new ArrayList<IResult>();
		}
		list.add(result);
		mResults.put(id, list);
	}

	static IResultService getService(IToolchainStorage storage) {
		assert storage != null;
		IStorable rtr = storage.getStorable(sKey);
		if (rtr == null) {
			rtr = new ResultService();
			storage.putStorable(sKey, rtr);
		}
		return (IResultService) rtr;
	}
	
	@Override
	public String toString() {
		if(mResults.size() == 0){
			return "No Results";
		}
		return mResults.toString();
	}

}
