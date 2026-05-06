package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class GhostVariableManager {

	private static final String LOCATION_VAR_PREFIX = "loc_";
	private static final int NOT_FORKED_LOCATION_ID = -1;

	private final ManagedScript mManagedScript;
	private final Map<IcfgLocation, Integer> mLocationIds;
	private final Map<String, IcfgLocation> mEntryLocations;
	private final Set<String> mImpreciseLocationThreads;
	private final Map<String, GhostProgramVar> mLocationVars = new HashMap<>();

	private GhostVariableManager(final ManagedScript managedScript, final Map<IcfgLocation, Integer> locationIds,
			final Map<String, IcfgLocation> entryLocations, final Set<String> impreciseLocationThreads) {
		mManagedScript = managedScript;
		mLocationIds = locationIds;
		mEntryLocations = entryLocations;
		mImpreciseLocationThreads = Set.copyOf(impreciseLocationThreads);
	}

	public static GhostVariableManager create(final ManagedScript managedScript,
			final Map<IcfgLocation, Integer> locationIds, final Set<String> threadIds,
			final Map<String, IcfgLocation> entryLocations, final PrimedDefaultIcfgSymbolTable symbolTable,
			final Set<String> impreciseLocationThreads, final boolean createLocations) {
		final GhostVariableManager manager =
				new GhostVariableManager(managedScript, locationIds, entryLocations, impreciseLocationThreads);
		if (createLocations) {
			managedScript.lock(manager);
			try {
				manager.initializeLocationVariables(threadIds, symbolTable);
			} finally {
				managedScript.unlock(manager);
			}
		}
		return manager;
	}

	private void initializeLocationVariables(final Set<String> threadIds,
			final PrimedDefaultIcfgSymbolTable symbolTable) {
		final Sort intSort = SmtSortUtils.getIntSort(mManagedScript.getScript());
		for (final String threadId : threadIds) {
			final String name = LOCATION_VAR_PREFIX + threadId;
			final GhostProgramVar locVar = GhostProgramVar.construct(name, intSort, mManagedScript, this);
			mLocationVars.put(threadId, locVar);
			symbolTable.registerGhostVariable(locVar);
		}
	}

	public TermVariable getLocationTermVar(final String threadId) {
		final GhostProgramVar var = mLocationVars.get(threadId);
		return var != null ? var.getTermVariable() : null;
	}

	public Set<TermVariable> getLocationTermVariables() {
		return mLocationVars.values().stream().map(GhostProgramVar::getTermVariable).collect(Collectors.toSet());
	}

	public Term createLocationConstraint(final String threadId, final IcfgLocation location) {
		if (!tracksLocationPrecisely(threadId)) {
			return mManagedScript.getScript().term("true");
		}
		return createLocationEquality(mLocationVars.get(threadId).getTermVariable(), location);
	}

	public Term createPrimedLocationConstraint(final String threadId, final IcfgLocation targetLocation,
			final PrimedDefaultIcfgSymbolTable symbolTable) {
		if (!tracksLocationPrecisely(threadId)) {
			return mManagedScript.getScript().term("true");
		}
		final TermVariable primedTv = symbolTable.getPrimedVar(mLocationVars.get(threadId));
		return createLocationEquality(primedTv, targetLocation);
	}

	public Term createNotForkedConstraint(final String threadId) {
		if (!tracksLocationPrecisely(threadId)) {
			return mManagedScript.getScript().term("true");
		}
		final Script script = mManagedScript.getScript();
		return SmtUtils.binaryEquality(script, mLocationVars.get(threadId).getTermVariable(),
				script.numeral(BigInteger.valueOf(NOT_FORKED_LOCATION_ID)));
	}

	public Term createInitialLocationState(final String mainThreadId) {
		final Script script = mManagedScript.getScript();
		final List<Term> conjuncts = new ArrayList<>();
		for (final Entry<String, GhostProgramVar> entry : mLocationVars.entrySet()) {
			if (!tracksLocationPrecisely(entry.getKey())) {
				continue;
			}
			final int locId;
			if (entry.getKey().equals(mainThreadId)) {
				locId = getAbstractLocation(mEntryLocations.get(entry.getKey()));
			} else {
				locId = NOT_FORKED_LOCATION_ID;
			}
			final Term locTerm = script.numeral(BigInteger.valueOf(locId));
			conjuncts.add(SmtUtils.binaryEquality(script, entry.getValue().getTermVariable(), locTerm));
		}
		return SmtUtils.and(script, conjuncts);
	}

	public IcfgLocation getEntryLocation(final String threadId) {
		return mEntryLocations.get(threadId);
	}

	private Term createLocationEquality(final TermVariable locVar, final IcfgLocation location) {
		final int abstractLoc = getAbstractLocation(location);
		final Script script = mManagedScript.getScript();
		return SmtUtils.binaryEquality(script, locVar, script.numeral(BigInteger.valueOf(abstractLoc)));
	}

	public boolean hasSameAbstractLocation(final IcfgLocation first, final IcfgLocation second) {
		return getAbstractLocation(first) == getAbstractLocation(second);
	}

	private int getAbstractLocation(final IcfgLocation location) {
		final Integer id = mLocationIds.get(location);
		if (id == null) {
			throw new IllegalStateException("Unknown ICFG location: " + location);
		}
		return id;
	}

	public Integer getAbstractLocationIdOrNull(final IcfgLocation location) {
		return mLocationIds.get(location);
	}

	public Map<IcfgLocation, Integer> getAbstractLocationIds() {
		return Map.copyOf(mLocationIds);
	}

	public boolean tracksLocationPrecisely(final String threadId) {
		return mLocationVars.containsKey(threadId) && !mImpreciseLocationThreads.contains(threadId);
	}
}
