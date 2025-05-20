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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class CfgPrecisionMetrics<UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private final Map<String, Integer> mPerThreadLocationCounterMap = new HashMap<>();
	private final ManagedScript mManagedScript;
	private final Script mScript;
	private final IIcfg<? extends LOC> mIcfg;
	private final Set<IProgramNonOldVar> mGlobals;
	private final IUltimateServiceProvider mServices;
	final Set<LOC> mCriticalLocationSet;
	final Set<IProgramVar> mRelationallyRelevantVars;

	public CfgPrecisionMetrics(final IUltimateServiceProvider services, final IIcfg<? extends LOC> icfg) {
		mManagedScript = icfg.getCfgSmtToolkit().getManagedScript();
		mScript = mManagedScript.getScript();
		mIcfg = icfg;
		mGlobals = mIcfg.getCfgSmtToolkit().getSymbolTable().getGlobals();
		mServices = services;
		mCriticalLocationSet = new HashSet<>();
		mRelationallyRelevantVars = new HashSet<>();
		collectCriticalLocationsAndRelationalVars(false);
	}

	public boolean locationIsInCriticalSection(final LOC loc) {
		return mCriticalLocationSet.contains(loc);
	}

	public Set<LOC> getCriticalSectionLocs() {
		return mCriticalLocationSet;
	}

	public boolean isRelationallyRelevant(final IProgramVar var) {
		return mRelationallyRelevantVars.contains(var);
	}

	public Set<IProgramVar> getRelationallyRelevantVars() {
		return mRelationallyRelevantVars;
	}

	private Map<LOC, Integer> collectCriticalLocationsAndRelationalVars(final boolean respectAfterGuard) {
		final Map<LOC, Integer> abstractLocationMapping = new HashMap<>();
		final var mutexGuardToVarsMap = computeMutexVars();
		final var mEntryLocs = mIcfg.getProcedureEntryNodes();
		boolean haveEnteredCritSection = false;
		for (final String thread : mEntryLocs.keySet()) {
			final var entryLoc = mEntryLocs.get(thread);
			final IcfgLocationIterator<LOC> iter = new IcfgLocationIterator<>(entryLoc);
			while (iter.hasNext()) {
				final LOC loc = iter.next();
				if (thread.equals("ULTIMATE.start")) {
					continue;
				}
				if (haveEnteredCritSection) {
					mCriticalLocationSet.add(loc);
				}
				if (mutexGuardToVarsMap.containsKey(loc)) {
					haveEnteredCritSection = true;
				}
			}
		}
		return abstractLocationMapping;
	}

	private Map<LOC, Set<IProgramVar>> computeMutexVars() {
		final Set<IProgramVar> mutexVarsIProgramVarrs = new LinkedHashSet<>();
		final Map<LOC, Set<IProgramVar>> mutexGuardToVarsMap = new HashMap<>();
		final var mEntryLocs = mIcfg.getProcedureEntryNodes();
		for (final LOC entryLoc : mEntryLocs.values()) {
			if (entryLoc.getProcedure().equals("ULTIMATE.start")) {
				continue;
			}
			final IcfgLocationIterator<LOC> iter = new IcfgLocationIterator<>(entryLoc);
			while (iter.hasNext()) {
				final LOC loc = iter.next();
				final var outgoing = loc.getOutgoingEdges();
				collectRelationalVars(outgoing);
				if (shouldDifferentiate(loc.getIncomingEdges())) {
					mCriticalLocationSet.add(loc);
				}
				if (shouldDifferentiate(outgoing)) {
					mCriticalLocationSet.add(loc);
					mutexVarsIProgramVarrs.addAll(getGuardVars(outgoing));
					mutexGuardToVarsMap.put(loc, getGuardVars(outgoing));
				}

			}
		}
		return mutexGuardToVarsMap;
	}

	public boolean shouldDifferentiate(final List<IcfgEdge> outgoing) {
		final var guards = outgoing.stream()
				.map(e -> TransFormulaUtils.computeGuardTerm(mServices, mManagedScript, e.getTransformula(), false))
				.toList();
		final var term = SmtUtils.simplify(mManagedScript, SmtUtils.or(mScript, guards), mServices,
				SimplificationTechnique.POLY_PAC);
		final var globals = mGlobals.stream().map(v -> v.getTermVariable()).collect(Collectors.toSet());
		return Arrays.stream(term.getFreeVars()).anyMatch(globals::contains);
	}

	public void collectRelationalVars(final List<IcfgEdge> outgoing) {
		final var guards = outgoing.stream()
				.map(e -> TransFormulaUtils.computeGuardTerm(mServices, mManagedScript, e.getTransformula(), false))
				.toList();
		final var globals = mGlobals.stream().map(v -> v.getTermVariable()).collect(Collectors.toSet());
		for (final Term guard : guards) {
			final var containedGlobalsInGuard = Arrays.stream(guard.getFreeVars()).filter(s -> globals.contains(s))
					.toList();
			if (containedGlobalsInGuard.size() > 1) {
				mRelationallyRelevantVars.addAll(getGuardVars(outgoing));
			}
		}
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
}
