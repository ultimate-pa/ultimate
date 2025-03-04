package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.SymmetricHashRelation;

public class AbstractInterferenceState<STATE extends IAbstractState<STATE>, ACTION> {
	private Map<String, Map<ACTION, STATE>> mInterferenceMapHashRelation;
	private final ManagedScript mManagedScript;

	private final SymmetricHashRelation<String> mActiveIfActive;
	private final Set<IcfgEdge> mSeenForks;
	private final Map<String, Integer> mActiveThreadInstances;
	private CfgSmtToolkit mToolkit;

	public AbstractInterferenceState(final ManagedScript script, final IIcfg<?> cfg) {
		mInterferenceMapHashRelation = new HashMap<>();
		mActiveIfActive = new SymmetricHashRelation<>();
		mManagedScript = script;
		mSeenForks = new HashSet<>();
		mActiveThreadInstances = new HashMap<>();
		mToolkit = cfg.getCfgSmtToolkit();
		for (final String thread : mToolkit.getProcedures()) {
			mActiveThreadInstances.put(thread, 0);
			mInterferenceMapHashRelation.put(thread, new HashMap<>());
		}
	}

	public AbstractInterferenceState(final AbstractInterferenceState<STATE, ACTION> other) {
		mInterferenceMapHashRelation = new HashMap<>();
		for (final String threadName : other.getInterferenceMapHashRelation().keySet()) {
			mInterferenceMapHashRelation.put(threadName, new HashMap<>());
			for (final ACTION action : other.getInterferenceMapHashRelation().get(threadName).keySet()) {
				final var otherState = other.getInterferenceMapHashRelation().get(threadName).get(action);
				mInterferenceMapHashRelation.get(threadName).put(action, otherState);
			}
		}
		mActiveIfActive = new SymmetricHashRelation<>(other.getActiveIfActive());
		mManagedScript = other.getManagedScript();
		mSeenForks = new HashSet<>(other.getSeenForks());
		mActiveThreadInstances = new HashMap<>(other.getActiveThreadInstances());
	}

	public AbstractInterferenceState(final AbstractInterferenceState<STATE, ACTION> other,
			final Map<String, Map<ACTION, STATE>> newMap) {
		mInterferenceMapHashRelation = newMap;
		mActiveIfActive = new SymmetricHashRelation<>(other.getActiveIfActive());
		mManagedScript = other.getManagedScript();
		mSeenForks = new HashSet<>(other.getSeenForks());
		mActiveThreadInstances = new HashMap<>(other.getActiveThreadInstances());
	}

	public void changeInterferences(final Map<String, Map<ACTION, STATE>> newMap) {
		mInterferenceMapHashRelation = newMap;
	}

	public void update(final String forker, final String forked) {
		mActiveIfActive.addPair(forker, forked);
		getActiveThreadInstances().put(forked, getActiveThreadInstances().get(forked) + 1);
		for (final String thread : mActiveIfActive.getImage(forker)) {
			mActiveIfActive.addPair(thread, forked);
		}
		for (final String thread : mActiveIfActive.getImage(forked)) {
			mActiveIfActive.addPair(thread, forker);
		}
	}

	public Map<ACTION, STATE> getInterferencesForThread(final String threadName) {
		return mInterferenceMapHashRelation.get(threadName);
	}

	public void addInterference(final String threadName, final ACTION transFormula, final STATE state) {
		if (mInterferenceMapHashRelation.get(threadName) == null) {
			mInterferenceMapHashRelation.put(threadName, new HashMap<>());
		}
		if (mInterferenceMapHashRelation.get(threadName).get(transFormula) == null) {
			mInterferenceMapHashRelation.get(threadName).put(transFormula, state);
		} else {
			mInterferenceMapHashRelation.get(threadName).put(transFormula, FixpointEngineConcurrentUtils
					.unionOnSharedVariables(state, mInterferenceMapHashRelation.get(threadName).get(transFormula)));
		}
	}

	public Map<String, Map<ACTION, STATE>> getInterferenceMapHashRelation() {
		return mInterferenceMapHashRelation;
	}

	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

	public Set<String> interferenceStrings() {
		return getInterferenceMapHashRelation().keySet().stream()
				.flatMap(
						thread -> getInterferencesForThread(thread).keySet().stream()
								.map(action -> "Thread " + thread + ": " + action + ": "
										+ mInterferenceMapHashRelation.get(thread).get(action)))
				.collect(Collectors.toSet());
	}

	public Set<IcfgEdge> getSeenForks() {
		return mSeenForks;
	}

	public Map<String, Integer> getActiveThreadInstances() {
		return mActiveThreadInstances;
	}

	public SymmetricHashRelation<String> getActiveIfActive() {
		return mActiveIfActive;
	}

	// TODO: implement properly, just temporary implementation to test
	public boolean isSubsetOf(final AbstractInterferenceState<STATE, ACTION> other) {
		for (final String threadName : mInterferenceMapHashRelation.keySet()) {
			final var interferenceMap = mInterferenceMapHashRelation.get(threadName);
			if (mInterferenceMapHashRelation.get(threadName) == null) {
				mInterferenceMapHashRelation.put(threadName, new HashMap<>());
			}
			if (other.getInterferencesForThread(threadName) == null) {
				other.getInterferenceMapHashRelation().put(threadName, new HashMap<>());
			}
			for (final ACTION interferenceTransition : interferenceMap.keySet()) {
				final boolean firstNull = interferenceMap.get(interferenceTransition) == null;
				final boolean secondNull =
						other.getInterferencesForThread(threadName).get(interferenceTransition) == null;
				if (!firstNull && secondNull) {
					return false;
				}
				if (firstNull && !secondNull) {
					return false;
				}
				if (firstNull && secondNull) {
					continue;
				}
				if (interferenceMap.get(interferenceTransition).isSubsetOf(
						other.getInterferencesForThread(threadName).get(interferenceTransition)) == SubsetResult.NONE) {
					return false;
				}
			}
		}
		return true;
	}
}
