package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.SymmetricHashRelation;

public class AbstractInterferenceState<STATE extends IAbstractState<STATE>, ACTION> {
	private Map<String, Map<ACTION, STATE>> mThreadInterferenceMap;
	private final ManagedScript mManagedScript;

	private final SymmetricHashRelation<String> mActiveIfActive;
	private final Map<String, Integer> mActiveThreadInstances;
	private CfgSmtToolkit mToolkit;

	public AbstractInterferenceState(final ManagedScript script, final IIcfg<?> cfg) {
		mThreadInterferenceMap = new HashMap<>();
		mActiveIfActive = new SymmetricHashRelation<>();
		mManagedScript = script;
		mActiveThreadInstances = new HashMap<>();
		mToolkit = cfg.getCfgSmtToolkit();
		for (final String thread : mToolkit.getProcedures()) {
			mActiveThreadInstances.put(thread, 0);
			mThreadInterferenceMap.put(thread, new HashMap<>());
		}
	}

	public AbstractInterferenceState(final AbstractInterferenceState<STATE, ACTION> other) {
		mThreadInterferenceMap = new HashMap<>();
		for (final String threadName : other.getInterferenceMapHashRelation().keySet()) {
			mThreadInterferenceMap.put(threadName, new HashMap<>());
			for (final ACTION action : other.getInterferenceMapHashRelation().get(threadName).keySet()) {
				final var otherState = other.getInterferenceMapHashRelation().get(threadName).get(action);
				mThreadInterferenceMap.get(threadName).put(action, otherState);
			}
		}
		mActiveIfActive = new SymmetricHashRelation<>(other.getActiveIfActive());
		mManagedScript = other.getManagedScript();
		mActiveThreadInstances = new HashMap<>(other.getActiveThreadInstances());
	}

	public AbstractInterferenceState(final AbstractInterferenceState<STATE, ACTION> other,
			final Map<String, Map<ACTION, STATE>> newMap) {
		mThreadInterferenceMap = newMap;
		mActiveIfActive = new SymmetricHashRelation<>(other.getActiveIfActive());
		mManagedScript = other.getManagedScript();
		mActiveThreadInstances = new HashMap<>(other.getActiveThreadInstances());
	}

	public void changeInterferences(final Map<String, Map<ACTION, STATE>> newMap) {
		mThreadInterferenceMap = newMap;
	}

	public void update(final String forker, final String forked) {
		mActiveThreadInstances.put(forked, mActiveThreadInstances.get(forked) + 1);
		mActiveIfActive.addPair(forker, forked);
		for (final String thread : mActiveIfActive.getImage(forker)) {
			mActiveIfActive.addPair(thread, forked);
		}
		for (final String thread : mActiveIfActive.getImage(forked)) {
			mActiveIfActive.addPair(thread, forker);
		}
	}

	public Map<ACTION, STATE> getInterferencesForThread(final String threadName) {
		return mThreadInterferenceMap.get(threadName);
	}

	public void addInterference(final String threadName, final ACTION transFormula, final STATE state) {
		if (mThreadInterferenceMap.get(threadName) == null) {
			mThreadInterferenceMap.put(threadName, new HashMap<>());
		}
		if (mThreadInterferenceMap.get(threadName).get(transFormula) == null) {
			mThreadInterferenceMap.get(threadName).put(transFormula, state);
		} else {
			mThreadInterferenceMap.get(threadName).put(transFormula, FixpointEngineConcurrentUtils
					.unionOnSharedVariables(state, mThreadInterferenceMap.get(threadName).get(transFormula)));
		}
	}

	public Map<String, Map<ACTION, STATE>> getInterferenceMapHashRelation() {
		return mThreadInterferenceMap;
	}

	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

	public Set<String> interferenceStrings() {
		return getInterferenceMapHashRelation().keySet().stream()
				.flatMap(thread -> getInterferencesForThread(thread).keySet().stream().map(action -> "Thread " + thread
						+ ": " + action + ": " + mThreadInterferenceMap.get(thread).get(action)))
				.collect(Collectors.toSet());
	}

	public Map<String, Integer> getActiveThreadInstances() {
		return mActiveThreadInstances;
	}

	public SymmetricHashRelation<String> getActiveIfActive() {
		return mActiveIfActive;
	}

	public boolean isSubsetOf(final AbstractInterferenceState<STATE, ACTION> other) {
		for (final String threadName : mThreadInterferenceMap.keySet()) {
			final Map<ACTION, STATE> thisInterferenceMap =
					mThreadInterferenceMap.getOrDefault(threadName, Collections.emptyMap());
			final Map<ACTION, STATE> otherInterferenceMap =
					other.getInterferenceMapHashRelation().getOrDefault(threadName, Collections.emptyMap());

			for (final ACTION action : thisInterferenceMap.keySet()) {
				final STATE thisState = thisInterferenceMap.get(action);
				final STATE otherState = otherInterferenceMap.get(action);

				if (thisState == null && otherState == null) {
					continue;
				}
				if (thisState == null || otherState == null) {
					return false;
				}
				if (thisState.isSubsetOf(otherState) == SubsetResult.NONE) {
					return false;
				}
			}
		}
		return true;
	}
}
