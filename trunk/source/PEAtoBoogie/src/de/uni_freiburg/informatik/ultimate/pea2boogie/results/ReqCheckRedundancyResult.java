package de.uni_freiburg.informatik.ultimate.pea2boogie.results;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.regex.Matcher;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

public class ReqCheckRedundancyResult<LOC extends IElement> extends ReqCheckFailResult<LOC> {

	private String mReqName;
	private String mRedundancySet;
	private static String mRegex = "[a-zA-Z_]+[a-zA-Z0-9_]*_ct(0|[1-9][0-9]*)[a-zA-Z0-9_]*_total";
	
	public ReqCheckRedundancyResult(LOC element, String plugin, String reqName, String redundancySet) {
		super(element, plugin);
		mReqName = reqName;
		mRedundancySet = redundancySet;
	}

	@Override
	public String getLongDescription() {
		return "Extracted redundancy set for " + mReqName + ": " + mRedundancySet;
	}
	
	/*
	 * Function that parses (loop/location) invariants represented by strings. In the terms of the regex,
	 * we extract every name of the automata appearing inside of the loop invariant.
	 * TODO: One issue that persist is if a user names the observable of a requirement
	 * such that it matches the regex (for example: "input FakeReq_ct0_total_pc IS bool").
	 * For now the method works under the assumption that names created during the formalization process are
	 * disjoint of the variable names used in the program that simulates the intersection of automata
	 */
	public static Set<String> extractRedundancySet(String invariant) {
		Pattern pattern = Pattern.compile(mRegex);
		Matcher matcher = pattern.matcher(invariant);
		
		Set<String> redundancySet = new LinkedHashSet<>();
		
		while (matcher.find()) {
			redundancySet.add(matcher.group().split("_ct")[0]);
		}
		
		return redundancySet;
	}
	
}
