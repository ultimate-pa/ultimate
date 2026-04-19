package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.GuardSplitBucketDomain.GuardBucketPolicy;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class GuardBucketPolicyProvider {
	private static final String MAIN_THREAD = "ULTIMATE.start";

	private GuardBucketPolicyProvider() {
	}

	public static Map<String, GuardBucketPolicy> computePolicies(final List<String> threadIds,
			final Map<IcfgLocation, Integer> locationIds, final GhostVariableManager ghostVars,
			final IIcfg<IcfgLocation> icfg) {
		final List<String> workerThreads = threadIds.stream().filter(t -> !MAIN_THREAD.equals(t)).sorted().toList();
		if (workerThreads.size() != 2 || !hasDirectMainTwoWorkerShape(workerThreads, icfg)) {
			return Map.of();
		}
		final Map<String, Set<Integer>> rawIdsByThread = collectRawLocationIdsByThread(locationIds);
		final String firstWorker = workerThreads.get(0);
		final String secondWorker = workerThreads.get(1);
		final Map<String, GuardBucketPolicy> policies = new LinkedHashMap<>();
		putPolicyIfPresent(policies, firstWorker, createGuardBucketPolicy(secondWorker, rawIdsByThread.get(secondWorker),
				ghostVars, icfg));
		putPolicyIfPresent(policies, secondWorker, createGuardBucketPolicy(firstWorker, rawIdsByThread.get(firstWorker),
				ghostVars, icfg));
		return policies;
	}

	private static void putPolicyIfPresent(final Map<String, GuardBucketPolicy> policies, final String threadId,
			final GuardBucketPolicy policy) {
		if (policy != null) {
			policies.put(threadId, policy);
		}
	}

	private static boolean hasDirectMainTwoWorkerShape(final List<String> workerThreads, final IIcfg<IcfgLocation> icfg) {
		final Map<String, Set<String>> directForkTargets = collectDirectForkTargets(icfg);
		final Set<String> mainForkTargets = directForkTargets.getOrDefault(MAIN_THREAD, Set.of());
		return mainForkTargets.size() == workerThreads.size() && mainForkTargets.containsAll(workerThreads)
				&& workerThreads.stream()
						.allMatch(workerThread -> directForkTargets.getOrDefault(workerThread, Set.of()).isEmpty());
	}

	private static Map<String, Set<String>> collectDirectForkTargets(final IIcfg<IcfgLocation> icfg) {
		final Map<String, Set<String>> forkTargetsByThread = new LinkedHashMap<>();
		for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			forkTargetsByThread.computeIfAbsent(fork.getSource().getProcedure(), __ -> new LinkedHashSet<>())
					.add(fork.getNameOfForkedProcedure());
		}
		return forkTargetsByThread;
	}

	private static Map<String, Set<Integer>> collectRawLocationIdsByThread(final Map<IcfgLocation, Integer> locationIds) {
		final Map<String, Set<Integer>> idsByThread = new LinkedHashMap<>();
		for (final var entry : locationIds.entrySet()) {
			idsByThread.computeIfAbsent(entry.getKey().getProcedure(), __ -> new LinkedHashSet<>()).add(entry.getValue());
		}
		return idsByThread;
	}

	private static GuardBucketPolicy createGuardBucketPolicy(final String peerThreadId, final Set<Integer> rawIds,
			final GhostVariableManager ghostVars, final IIcfg<IcfgLocation> icfg) {
		if (rawIds == null || rawIds.isEmpty()) {
			return null;
		}
		final TermVariable bucketVariable = ghostVars.getLocationTermVar(peerThreadId);
		if (bucketVariable == null) {
			return null;
		}
		final Integer entryId = ghostVars.getAbstractLocationIdOrNull(ghostVars.getEntryLocation(peerThreadId));
		final IcfgLocation exitLocation = icfg.getProcedureExitNodes().get(peerThreadId);
		final Integer exitId = exitLocation == null ? null : ghostVars.getAbstractLocationIdOrNull(exitLocation);
		final Map<Integer, Integer> rawToBucket = computeRawToBucketMap(rawIds, entryId, exitId);
		if (rawToBucket == null) {
			return null;
		}
		final Map<Integer, Set<Integer>> bucketToRawValues = new LinkedHashMap<>();
		for (final var entry : rawToBucket.entrySet()) {
			bucketToRawValues.computeIfAbsent(entry.getValue(), __ -> new LinkedHashSet<>()).add(entry.getKey());
		}
		if (bucketToRawValues.size() <= 1) {
			return null;
		}
		return new GuardBucketPolicy(peerThreadId, bucketVariable, rawToBucket, bucketToRawValues);
	}

	private static Map<Integer, Integer> computeRawToBucketMap(final Set<Integer> rawIds, final Integer entryId,
			final Integer exitId) {
		final List<Integer> orderedIds = rawIds.stream().sorted().toList();
		final Map<Integer, Integer> rawToBucket = new LinkedHashMap<>();
		for (final Integer rawId : orderedIds) {
			rawToBucket.put(rawId, rawId);
		}
		if (orderedIds.size() > 3) {
			if (orderedIds.size() != 4 || exitId == null || !rawToBucket.containsKey(exitId)) {
				return null;
			}
			final Integer collapsedExitBucket = chooseCollapsedExitBucket(orderedIds, entryId, exitId);
			if (collapsedExitBucket == null) {
				return null;
			}
			rawToBucket.put(exitId, collapsedExitBucket);
		}
		if (entryId != null && rawToBucket.containsKey(entryId)) {
			rawToBucket.put(-1, rawToBucket.get(entryId));
		}
		if (new HashSet<>(rawToBucket.values()).size() > 3) {
			return null;
		}
		return rawToBucket;
	}

	private static Integer chooseCollapsedExitBucket(final List<Integer> orderedIds, final Integer entryId,
			final Integer exitId) {
		Integer candidate = null;
		for (final Integer rawId : orderedIds) {
			if (rawId.equals(exitId)) {
				continue;
			}
			if (entryId != null && rawId.equals(entryId)) {
				continue;
			}
			candidate = rawId;
		}
		if (candidate != null) {
			return candidate;
		}
		for (final Integer rawId : orderedIds) {
			if (!rawId.equals(exitId)) {
				return rawId;
			}
		}
		return null;
	}
}
