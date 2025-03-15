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

public class AbstractInterferenceState<STATE extends IAbstractState<STATE>, ACTION> {
	private Map<String, Map<ACTION, STATE>> mThreadInterferenceMap;
	private final ManagedScript mManagedScript;

	private CfgSmtToolkit mToolkit;

	public AbstractInterferenceState(final ManagedScript script, final IIcfg<?> cfg) {
		mThreadInterferenceMap = new HashMap<>();
		mManagedScript = script;
		mToolkit = cfg.getCfgSmtToolkit();
		for (final String thread : mToolkit.getProcedures()) {
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
		mManagedScript = other.getManagedScript();
	}

	public void changeInterferences(final Map<String, Map<ACTION, STATE>> newMap) {
		mThreadInterferenceMap = newMap;
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

	public boolean isSubsetOf(final AbstractInterferenceState<STATE, ACTION> other) {
		for (final String threadName : mThreadInterferenceMap.keySet()) {
			final Map<ACTION, STATE> thisInterferenceMap = mThreadInterferenceMap.getOrDefault(threadName,
					Collections.emptyMap());
			final Map<ACTION, STATE> otherInterferenceMap = other.getInterferenceMapHashRelation()
					.getOrDefault(threadName, Collections.emptyMap());

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

	public Set<String> interferenceStrings() {
		return getInterferenceMapHashRelation().keySet().stream()
				.flatMap(thread -> getInterferencesForThread(thread).keySet().stream().map(action -> "Thread " + thread
						+ ": " + action + ": " + mThreadInterferenceMap.get(thread).get(action)))
				.collect(Collectors.toSet());
	}

}
