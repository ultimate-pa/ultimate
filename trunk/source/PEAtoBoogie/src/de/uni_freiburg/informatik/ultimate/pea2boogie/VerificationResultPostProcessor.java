package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;

public class VerificationResultPostProcessor {

	private final HashMap<String, Set<String>> mReqIdToVars;
	
	public VerificationResultPostProcessor(final HashMap<String, List<PhaseEventAutomata>> reqIdToPeas) {
		mReqIdToVars = new HashMap<String, Set<String>>();
		reqIdToPeas.forEach((id, peas) -> {
			var varSet = new HashSet<String>();
			for (var pea : peas) {
				varSet.addAll(pea.getVariables().keySet());
			}
			mReqIdToVars.put(id, varSet);
		});
	}
	
	public Set<String> variableAnalysis(String redundantId, Set<String> redundancySet) {
		final var varToReqs = getVarToReqs(redundancySet);
		final var newSet = new HashSet<String>();
		Queue<String> fifo = new LinkedList<>();
		newSet.add(redundantId);
		fifo.add(redundantId);
		
		while (!fifo.isEmpty()) {
			var reqId = fifo.poll();
			var vars = mReqIdToVars.get(reqId);
			for (var v : vars) {
				var reqSet = varToReqs.get(v);
				for (var r : reqSet) {
					if (!newSet.contains(r)) {
						newSet.add(r);
						fifo.add(r);
					}
				}
			}
		}
		return newSet;
	}
	
	
	private HashMap<String, Set<String>> getVarToReqs(Set<String> redundancySet) {
		final var varToReqs = new HashMap<String, Set<String>>();
		for (var reqId : redundancySet) {
			for (var variable : mReqIdToVars.get(reqId)) {
				if (varToReqs.containsKey(variable)) {
					varToReqs.get(variable).add(reqId);
				} else {
					var idSet = new HashSet<String>();
					idSet.add(reqId);
					varToReqs.put(variable, idSet);
				}
			}
		}
		return varToReqs;
	}
}
