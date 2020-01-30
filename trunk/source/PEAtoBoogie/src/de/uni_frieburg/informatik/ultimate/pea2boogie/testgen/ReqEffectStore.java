package de.uni_frieburg.informatik.ultimate.pea2boogie.testgen;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class ReqEffectStore {

	private final Set<String> mEffectVars;
	private final Set<Integer> mEffectPhase;
	private final Set<Integer> mOutputEffectPhase;
	private final Map<Integer, Integer> mEffectEdges;
	private final Map<Integer, Integer> mOutputEffectEdges;

	public ReqEffectStore() {
		mEffectPhase = new HashSet<Integer>();
		mOutputEffectPhase = new HashSet<Integer>();
		mEffectVars = new HashSet<String>();
		mEffectEdges = new HashMap<Integer, Integer>();
		mOutputEffectEdges = new HashMap<Integer, Integer>();
	}

	public void addEffectVars(Set<String> effectVars) {
		mEffectVars.addAll(effectVars);
	}

	public void addEffectPhaseIndex(Integer phaseIndex) {
		mEffectPhase.add(phaseIndex);
	}

	public void addOutputEffectPhaseIndex(Integer phaseIndex) {
		mOutputEffectPhase.add(phaseIndex);
	}

	public void addEffectEdgeIndex(Integer sourcePhaseIndex, Integer targetPhaseIndex) {
		mEffectEdges.put(sourcePhaseIndex, targetPhaseIndex);
	}

	public void addOutputEffectEdgeIndex(Integer sourcePhaseIndex, Integer targetPhaseIndex) {
		mOutputEffectEdges.put(sourcePhaseIndex, targetPhaseIndex);
	}

	public Set<String> getEffectVars() {
		return mEffectVars;
	}

	public boolean isEffectPhaseIndex(Integer phaseIndex) {
		return mEffectPhase.contains(phaseIndex);
	}

	public  Set<Integer> getEffectPhaseIndexes() {
		return mEffectPhase;
	}

	public  Set<Integer> getEffectEdgeSourceIndexes() {
		return mEffectEdges.keySet();
	}

	public boolean isOutputEffectPhaseIndex(Integer phaseIndex) {
		return mOutputEffectPhase.contains(phaseIndex);
	}

	public Set<Integer> getOutputEffectPhaseIndex(){
		return mOutputEffectPhase;
	}

	public boolean isEffectEdge(Integer sourcePhaseIndex, Integer targetPhaseIndex) {
		return mEffectEdges.containsKey(sourcePhaseIndex) &&
				mEffectEdges.get(sourcePhaseIndex) == targetPhaseIndex;
	}

	public boolean isOutputEffectEdge(Integer sourcePhaseIndex, Integer targetPhaseIndex) {
		return mOutputEffectEdges.containsKey(sourcePhaseIndex) &&
				mOutputEffectEdges.get(sourcePhaseIndex) == targetPhaseIndex;
	}

}
