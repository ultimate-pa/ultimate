package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

// TODO Threadcounters
/** Manages ghost location variables for thread-modular analysis. */
public class GhostVariableManager {

	private static final String LOCATION_VAR_PREFIX = "loc_";

	private final ManagedScript mManagedScript;
	private final Map<IcfgLocation, Integer> mLocationIds;
	private final Map<String, GhostProgramVar> mLocationVars = new HashMap<>();

	private GhostVariableManager(final ManagedScript managedScript, final Map<IcfgLocation, Integer> locationIds) {
		mManagedScript = managedScript;
		mLocationIds = locationIds;
	}

	public static GhostVariableManager create(final ManagedScript managedScript,
			final Map<IcfgLocation, Integer> locationIds, final Set<String> threadIds,
			final PrimedDefaultIcfgSymbolTable symbolTable) {
		final GhostVariableManager manager = new GhostVariableManager(managedScript, locationIds);
		manager.initializeVariables(threadIds, symbolTable);
		return manager;
	}

	private void initializeVariables(final Set<String> threadIds, final PrimedDefaultIcfgSymbolTable symbolTable) {
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
		final Set<TermVariable> result = new HashSet<>();
		for (final GhostProgramVar pv : mLocationVars.values()) {
			result.add(pv.getTermVariable());
		}
		return result;
	}

	/** loc_threadId = alpha(location) */
	public Term createLocationConstraint(final String threadId, final IcfgLocation location) {
		return createLocationEquality(mLocationVars.get(threadId).getTermVariable(), location);
	}

	/** loc_threadId' = alpha(location) */
	public Term createPrimedLocationConstraint(final String threadId, final IcfgLocation targetLocation,
			final PrimedDefaultIcfgSymbolTable symbolTable) {
		final TermVariable primedTv = symbolTable.getPrimedVar(mLocationVars.get(threadId));
		return createLocationEquality(primedTv, targetLocation);
	}

	/** loc_thread = 1 (entry location) for all threads. */
	public Term createAllLocationsAtEntry() {
		final Script script = mManagedScript.getScript();
		final Term one = script.numeral(BigInteger.ONE);
		final List<Term> conjuncts = new ArrayList<>();
		for (final GhostProgramVar locVar : mLocationVars.values()) {
			conjuncts.add(SmtUtils.binaryEquality(script, locVar.getTermVariable(), one));
		}
		return SmtUtils.and(script, conjuncts);
	}

	private Term createLocationEquality(final TermVariable locVar, final IcfgLocation location) {
		final int abstractLoc = getAbstractLocation(location);
		final Script script = mManagedScript.getScript();
		final Term abstractLocTerm = script.numeral(BigInteger.valueOf(abstractLoc));
		return SmtUtils.binaryEquality(script, locVar, abstractLocTerm);
	}

	private int getAbstractLocation(final IcfgLocation location) {
		final Integer id = mLocationIds.get(location);
		if (id == null) {
			throw new IllegalStateException("Unknown ICFG location: " + location);
		}
		return id;
	}
}
