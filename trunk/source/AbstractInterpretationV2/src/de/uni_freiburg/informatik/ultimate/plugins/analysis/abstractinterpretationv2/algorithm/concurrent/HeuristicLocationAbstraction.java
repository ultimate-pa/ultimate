package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class HeuristicLocationAbstraction<LOC extends IcfgLocation> {
	private final Map<String, Integer> mPerThreadLocationCounterMap = new HashMap<>();
	private final ManagedScript mManagedScript;
	private final Script mScript;
	private final IIcfg<? extends LOC> mIcfg;
	private final Set<IProgramNonOldVar> mGlobals;
	private final IUltimateServiceProvider mServices;
	private final Map<LOC, Integer> mMutexVarSplitMapWithExitMarked;
	final Map<String, Set<IProgramVar>> mWrittenByThread = new HashMap<>();

	public HeuristicLocationAbstraction(final IUltimateServiceProvider services, final IIcfg<? extends LOC> icfg) {
		mManagedScript = icfg.getCfgSmtToolkit().getManagedScript();
		mScript = mManagedScript.getScript();
		mIcfg = icfg;
		mGlobals = mIcfg.getCfgSmtToolkit().getSymbolTable().getGlobals();
		mServices = services;
		for (final String thread : mIcfg.getProcedureEntryNodes().keySet()) {
			mWrittenByThread.put(thread, new HashSet<>());
			mPerThreadLocationCounterMap.put(thread, 0);
		}
		mMutexVarSplitMapWithExitMarked = broadMutexSplitting();
	}

	/*
	 * Location-abstraction algorithm: Increment location-abstraction counter label at any location which contains a
	 * potential mutex guard, or any location which writes or reads a variable contained in a mutex guard, if it occurs
	 * before a mutex guard.
	 */
	public StaticAbstractLocationMap<LOC> mutexVarSplitting() {
		return new StaticAbstractLocationMap<>(this::mutexVarSplitFun, mIcfg);
	}

	private int mutexVarSplitFun(final LOC loc) {
		return mMutexVarSplitMapWithExitMarked.get(loc);
	}

	private int getThreadLocationCounter(final String thread) {
		return mPerThreadLocationCounterMap.getOrDefault(thread, 0);
	}

	private int getAndIncrementThreadLocationCounter(final String thread) {
		final int counter = mPerThreadLocationCounterMap.getOrDefault(thread, -1);
		mPerThreadLocationCounterMap.put(thread, counter + 1);
		return counter;
	}

	private Map<LOC, Integer> broadMutexSplitting() {
		final Map<LOC, Integer> abstractLocationMapping = new HashMap<>();
		final var mutexGuardToVarsMap = computeMutexVars();
		final var mEntryLocs = mIcfg.getProcedureEntryNodes();
		for (final String thread : mEntryLocs.keySet()) {
			boolean seenOneGuard = false;
			final var entryLoc = mEntryLocs.get(thread);
			final IcfgLocationIterator<LOC> iter = new IcfgLocationIterator<>(entryLoc);
			while (iter.hasNext()) {
				final LOC loc = iter.next();
				if (mutexGuardToVarsMap.containsKey(loc)) {
					abstractLocationMapping.put(loc, getAndIncrementThreadLocationCounter(thread));
					seenOneGuard = true;
				} else if (seenOneGuard && containsRelevantVar(loc.getOutgoingEdges(), mutexGuardToVarsMap)) {
					abstractLocationMapping.put(loc, getAndIncrementThreadLocationCounter(thread));
					seenOneGuard = false;
				} else {
					abstractLocationMapping.put(loc, getThreadLocationCounter(thread));
				}
			}
		}
		return abstractLocationMapping;
	}

	/*
	 * Computes for each location which contains an (assumed) mutex or similarily critical, flag-like location, the set
	 * of Program variables used for the mutex.
	 */
	private Map<LOC, Set<IProgramVar>> computeMutexVars() {
		final Set<IProgramVar> mutexVarsIProgramVarrs = new LinkedHashSet<>();
		final Map<LOC, Set<IProgramVar>> mutexGuardToVarsMap = new HashMap<>();
		final var mEntryLocs = mIcfg.getProcedureEntryNodes();
		for (final LOC entryLoc : mEntryLocs.values()) {
			final IcfgLocationIterator<LOC> iter = new IcfgLocationIterator<>(entryLoc);
			while (iter.hasNext()) {
				final LOC loc = iter.next();
				final var outgoing = loc.getOutgoingEdges();
				if (shouldDifferentiate(outgoing)) {
					mutexVarsIProgramVarrs.addAll(getGuardVars(outgoing));
					mutexGuardToVarsMap.put(loc, getGuardVars(outgoing));
				}
				final var writtenGlobals = outgoing.stream()
						.flatMap(e -> e.getTransformula().getOutVars().keySet().stream()).filter(mGlobals::contains)
						.collect(Collectors.toSet());
				mWrittenByThread.get(loc.getProcedure()).addAll(writtenGlobals);

			}
		}
		return mutexGuardToVarsMap;
	}

	private boolean containsRelevantVar(final List<IcfgEdge> outgoing,
			final Map<LOC, Set<IProgramVar>> mutexGuardToVarsMap) {
		final var vars = outgoing.stream().flatMap(e -> e.getTransformula().getAssignedVars().stream())
				.collect(Collectors.toSet());
		return mutexGuardToVarsMap.entrySet().stream()
				.anyMatch(entry -> entry.getValue().stream().anyMatch(vars::contains));
	}

	public Set<IProgramVar> getGuardVars(final List<IcfgEdge> outgoing) {
		final var guards = outgoing.stream()
				.map(e -> TransFormulaUtils.computeGuardTerm(mServices, mManagedScript, e.getTransformula(), false))
				.toList();
		final var term = SmtUtils.simplify(mManagedScript, SmtUtils.or(mScript, guards), mServices,
				SimplificationTechnique.POLY_PAC);
		final Map<TermVariable, IProgramVar> termToGlobalMap = mGlobals.stream()
				.collect(Collectors.toMap(IProgramVar::getTermVariable, v -> v));
		final var freeVars = Arrays.stream(term.getFreeVars()).filter(termToGlobalMap::containsKey)
				.map(termToGlobalMap::get).collect(Collectors.toSet());
		return freeVars;
	}

	/*
	 * Computes if the outgoing edges of a location contain a guarded term of global variables. Used to look for
	 * possible Mutex/ other critical locations.
	 */
	public boolean shouldDifferentiate(final List<IcfgEdge> outgoing) {
		final var guards = outgoing.stream()
				.map(e -> TransFormulaUtils.computeGuardTerm(mServices, mManagedScript, e.getTransformula(), false))
				.toList();
		final var term = SmtUtils.simplify(mManagedScript, SmtUtils.or(mScript, guards), mServices,
				SimplificationTechnique.POLY_PAC);
		final var globals = mGlobals.stream().map(v -> v.getTermVariable()).collect(Collectors.toSet());
		return Arrays.stream(term.getFreeVars()).anyMatch(globals::contains);
	}
}