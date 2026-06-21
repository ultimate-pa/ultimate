package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

// Handles per-partition location updates after abstract-location changes and fork transitions.
public final class AbstractLocationPartitionedLocationUpdater {
	private final SymbolicTools mTools;
	private final GhostVariableManager mGhostVariables;

	public AbstractLocationPartitionedLocationUpdater(final SymbolicTools tools,
			final GhostVariableManager ghostVariables) {
		mTools = tools;
		mGhostVariables = ghostVariables;
	}

	public IPredicate updatePartitions(final AbstractLocationPartitionedPredicate partitionedPredicate,
			final String threadId, final IcfgLocation targetLocation, final int targetAbstractId,
			final AbstractLocationPartitionedDomain partitionedDomain) {
		final String locVarName = mGhostVariables.getLocationTermVar(threadId).getName();
		final Map<GlobalLocationState, IPredicate> result = new LinkedHashMap<>();
		for (final var partition : partitionedPredicate.partitions().entrySet()) {
			final IPredicate updatedValue = updatePartitionValue(partition.getValue(), threadId,
					targetLocation);
			final Map<String, Integer> newLocs = new LinkedHashMap<>(partition.getKey().locs());
			newLocs.put(locVarName, targetAbstractId);
			result.merge(new GlobalLocationState(newLocs), updatedValue, partitionedDomain.underlyingDomain()::join);
		}
		return partitionedDomain.buildPredicateFromPartitionsMap(result);
	}

	private IPredicate updatePartitionValue(final IPredicate postState, final String threadId,
			final IcfgLocation targetLocation) {
		final Term locConstraint = mGhostVariables.createLocationConstraint(threadId, targetLocation);
		if (SmtUtils.isTrueLiteral(postState.getFormula())) {
			return mTools.predicate(locConstraint);
		}
		final TermVariable currentLocTv = mGhostVariables.getLocationTermVar(threadId);
		final Term projected = overapproximateProjection(postState.getFormula(), currentLocTv);
		return mTools.predicate(SmtUtils.and(mTools.getScript(), projected, locConstraint));
	}

	private Term overapproximateProjection(final Term term, final TermVariable locVar) {
		if (!containsFreeVar(term, locVar)) {
			return term;
		}
		if (term instanceof final ApplicationTerm app) {
			return projectApplication(app, locVar);
		}
		if (term instanceof final QuantifiedFormula qf) {
			return projectQuantifier(qf, locVar);
		}
		return trueTerm();
	}

	private Term projectApplication(final ApplicationTerm app, final TermVariable locVar) {
		return switch (app.getFunction().getName()) {
		case "and" -> projectConjunction(app.getParameters(), locVar);
		case "or" -> projectDisjunction(app.getParameters(), locVar);
		default -> trueTerm();
		};
	}

	private Term projectConjunction(final Term[] conjuncts, final TermVariable locVar) {
		final ArrayList<Term> keptConjuncts = new ArrayList<>();
		for (final Term conjunct : conjuncts) {
			final Term projected = overapproximateProjection(conjunct, locVar);
			if (!SmtUtils.isTrueLiteral(projected)) {
				keptConjuncts.add(projected);
			}
		}
		if (keptConjuncts.isEmpty()) {
			return trueTerm();
		}
		return SmtUtils.and(mTools.getScript(), keptConjuncts);
	}

	private Term projectDisjunction(final Term[] disjuncts, final TermVariable locVar) {
		final ArrayList<Term> projectedDisjuncts = new ArrayList<>();
		for (final Term disjunct : disjuncts) {
			projectedDisjuncts.add(overapproximateProjection(disjunct, locVar));
		}
		return SmtUtils.or(mTools.getScript(), projectedDisjuncts);
	}

	private Term projectQuantifier(final QuantifiedFormula qf, final TermVariable locVar) {
		if (Arrays.asList(qf.getVariables()).contains(locVar)) {
			return qf;
		}
		return mTools.getScript().quantifier(qf.getQuantifier(), qf.getVariables(),
				overapproximateProjection(qf.getSubformula(), locVar));
	}

	private Term trueTerm() {
		return mTools.getScript().term("true");
	}

	private static boolean containsFreeVar(final Term term, final TermVariable var) {
		return Arrays.asList(term.getFreeVars()).contains(var);
	}
}
