package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ReqEffectStore {

	private final Set<String> mEffectVars;
	private final Set<Integer> mEffectPhase;
	private final Set<Integer> mOutputEffectPhase;
	private final Set<Pair<Integer, Integer>> mEffectEdges;
	private final Set<Pair<Integer, Integer>> mOutputEffectEdges;

	public ReqEffectStore() {
		mEffectPhase = new HashSet<>();
		mOutputEffectPhase = new HashSet<>();
		mEffectVars = new HashSet<>();
		mEffectEdges = new HashSet<>();
		mOutputEffectEdges = new HashSet<>();
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
		mEffectEdges.add(new Pair<>(sourcePhaseIndex, targetPhaseIndex));
	}

	public void addOutputEffectEdgeIndex(final Integer sourcePhaseIndex, final Integer targetPhaseIndex) {
		mOutputEffectEdges.add(new Pair<>(sourcePhaseIndex, targetPhaseIndex));
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
		return mEffectEdges.stream().map(p -> p.getFirst()).collect(Collectors.toSet());
	}

	public Set<Pair<Integer, Integer>> getEffectEdges() {
		return mEffectEdges;
	}

	public boolean isOutputEffectPhaseIndex(final Integer phaseIndex) {
		return mOutputEffectPhase.contains(phaseIndex);
	}

	public Set<Integer> getOutputEffectPhaseIndex() {
		return mOutputEffectPhase;
	}

	public Set<Pair<Integer, Integer>> getOutputEffectEdges() {
		return mOutputEffectEdges;
	}

	public boolean isEffectEdge(final Integer sourcePhaseIndex, final Integer targetPhaseIndex) {
		return mEffectEdges.contains(new Pair<>(sourcePhaseIndex, targetPhaseIndex));
	}

	public boolean isOutputEffectEdge(final Integer sourcePhaseIndex, final Integer targetPhaseIndex) {
		return mOutputEffectEdges.contains(new Pair<>(sourcePhaseIndex, targetPhaseIndex));
	}

}
