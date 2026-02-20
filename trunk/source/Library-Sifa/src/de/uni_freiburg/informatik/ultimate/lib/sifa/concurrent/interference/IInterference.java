package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

public interface IInterference {
	Collection<IPredicate> getPredicates();

	IInterference build(String threadId, Map<IcfgLocation, IPredicate> locationStates, InterferenceFactory factory);

	boolean isTrivial();

	boolean isSubsumedBy(IInterference other, IDomain domain);

	IInterference widen(IInterference other, IDomain domain);

	int size();

	default Set<Integer> getSourceAbsLocations() {
		return Set.of();
	}

	default Set<Integer> getTargetAbsLocations() {
		return Set.of();
	}

	/** Apply this interference relation until a local fixpoint */
	IPredicate applyUntilFixpoint(IPredicate state, IDomain domain, RelationalPredicatePostcondition postcondition,
			GhostVariableManager ghostVars, ManagedScript managedScript, BasicPredicateFactory factory,
			int wideningThreshold, SifaStats stats);
}
