package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

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
		mEffectPhase = new HashSet<>();
		mOutputEffectPhase = new HashSet<>();
		mEffectVars = new HashSet<>();
		mEffectEdges = new HashMap<>();
		mOutputEffectEdges = new HashMap<>();
	}

	public void addEffectVars(final Set<String> effectVars) {
		mEffectVars.addAll(effectVars);
	}

	public void addEffectPhaseIndex(final Integer phaseIndex) {
		mEffectPhase.add(phaseIndex);
	}

	public void addOutputEffectPhaseIndex(final Integer phaseIndex) {
		mOutputEffectPhase.add(phaseIndex);
	}

	public void addEffectEdgeIndex(final Integer sourcePhaseIndex, final Integer targetPhaseIndex) {
		mEffectEdges.put(sourcePhaseIndex, targetPhaseIndex);
	}

	public void addOutputEffectEdgeIndex(final Integer sourcePhaseIndex, final Integer targetPhaseIndex) {
		mOutputEffectEdges.put(sourcePhaseIndex, targetPhaseIndex);
	}

	public Set<String> getEffectVars() {
		return mEffectVars;
	}

	public boolean isEffectPhaseIndex(final Integer phaseIndex) {
		return mEffectPhase.contains(phaseIndex);
	}

	public Set<Integer> getEffectPhaseIndexes() {
		return mEffectPhase;
	}

	public Set<Integer> getEffectEdgeSourceIndexes() {
		return mEffectEdges.keySet();
	}

	public Map<Integer, Integer> getEffectEdges() {
		return mEffectEdges;
	}

	public boolean isOutputEffectPhaseIndex(final Integer phaseIndex) {
		return mOutputEffectPhase.contains(phaseIndex);
	}

	public Set<Integer> getOutputEffectPhaseIndex() {
		return mOutputEffectPhase;
	}

	public boolean isEffectEdge(final Integer sourcePhaseIndex, final Integer targetPhaseIndex) {
		return mEffectEdges.containsKey(sourcePhaseIndex) && mEffectEdges.get(sourcePhaseIndex) == targetPhaseIndex;
	}

	public boolean isOutputEffectEdge(final Integer sourcePhaseIndex, final Integer targetPhaseIndex) {
		return mOutputEffectEdges.containsKey(sourcePhaseIndex)
				&& mOutputEffectEdges.get(sourcePhaseIndex) == targetPhaseIndex;
	}

}
