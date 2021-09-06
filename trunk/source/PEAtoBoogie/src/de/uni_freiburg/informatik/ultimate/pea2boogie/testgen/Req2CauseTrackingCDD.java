package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.BoogieBooleanExpressionDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

public class Req2CauseTrackingCDD {

	private final Map<String, String> mTrackingVars;
	private final ILogger mLogger;

	public Req2CauseTrackingCDD(final ILogger logger) {
		mTrackingVars = new HashMap<>();
		mLogger = logger;
	}

	/*
	 * Add tracking guards to the invariant. Note that no tracking vars are added for: inputs, constants Tracking vars
	 * are only added for the requirements effect vars if this is no effect phase.
	 */
	public CDD transformInvariantTracking(final CDD cdd, final Set<String> trackedVars, final Set<String> effectVars,
			final boolean isEffectPhase) {
		final CDD[] conjuncts = cdd.toDNF();
		if (conjuncts.length > 1 && isEffectPhase) {
			final Set<CDD> effectConjuncts = getEffectConjuncts(conjuncts, effectVars);
			if (hasDeterministicEffect(conjuncts, effectVars)) {
				// get effect part
				final CDD result = effectConjuncts.stream().reduce(CDD.TRUE, (a, b) -> {
					return a.and(b);
				});
				// and force trigger to be triggered
				final Set<CDD> triggerConjuncts = getTriggerConjuncts(conjuncts, effectVars);
				final CDD intermed = result.and(triggerConjuncts.stream().reduce(CDD.TRUE, (a, b) -> {
					return a.and(b.negate());
				}));
				return addTrackingGuards(result.and(intermed), trackedVars);
			}
			mLogger.error("Nondet. effect (will not build lower Automaton): " + effectConjuncts);
			return CDD.FALSE;
		}
		return addTrackingGuards(cdd, trackedVars);
	}

	private static Set<CDD> getEffectConjuncts(final CDD[] conjuncts, final Set<String> effectVars) {
		final Set<CDD> effectDisjuncts = new HashSet<>();
		for (final CDD cdd : conjuncts) {
			final Set<String> effectVarsOfCDD = getCddVariables(cdd);
			effectVarsOfCDD.retainAll(effectVars);
			if (effectVarsOfCDD.size() > 0) {
				effectDisjuncts.add(cdd);
			}
		}
		return effectDisjuncts;
	}

	private static Set<CDD> getTriggerConjuncts(final CDD[] conjuncts, final Set<String> effectVars) {
		final Set<CDD> triggerDisjuncts = new HashSet<>();
		for (final CDD cdd : conjuncts) {
			final Set<String> triggerVars = getCddVariables(cdd);
			if (!triggerVars.removeAll(effectVars)) { // only add if removing effects dones not change set of vars
				triggerDisjuncts.add(cdd);
			}
		}
		return triggerDisjuncts;
	}

	private CDD addTrackingGuards(final CDD cdd, final Set<String> trackedVars) {
		if (cdd == CDD.TRUE || cdd == CDD.FALSE) {
			return cdd;
		}

		final List<CDD> newChildren = new ArrayList<>();
		if (cdd.getChilds() != null) {
			for (final CDD child : cdd.getChilds()) {
				newChildren.add(addTrackingGuards(child, trackedVars));
			}
		}
		final CDD annotatedCDD = CDD.create(cdd.getDecision(), newChildren.toArray(new CDD[newChildren.size()]));

		CDD trackGuard = CDD.TRUE;
		for (final String v : getVarsFromDecision(cdd.getDecision())) {
			if (trackedVars.contains(v)) {
				final String varName = ReqTestAnnotator.TRACKING_VAR_PREFIX + v;
				// TODO more elegant way to check if its a primed var
				if (!v.endsWith("'")) {
					mTrackingVars.put(varName, "bool");
				}
				trackGuard = trackGuard.and(BooleanDecision.create(varName));
			}
		}
		mLogger.info("Track guard for (" + cdd + ") is :" + trackGuard);
		return annotatedCDD.and(trackGuard);
	}

	/*
	 * Transforms a CDD containing a range decision as follows: - t <= c to t >= c
	 *
	 * Note: if the CDD is no range decision, this will return CDD.True
	 */
	public CDD upperToLowerBoundCdd(final CDD cdd, final boolean dropOther) {
		if (cdd == CDD.TRUE || cdd == CDD.FALSE) {
			return cdd;
		}

		final List<CDD> newChildren = new ArrayList<>();
		if (cdd.getChilds() != null) {
			for (final CDD child : cdd.getChilds()) {
				newChildren.add(upperToLowerBoundCdd(child, dropOther));
			}
		}
		final CDD[] children = newChildren.toArray(new CDD[newChildren.size()]);
		final Decision<?> decision = cdd.getDecision();
		if (decision instanceof RangeDecision) {
			CDD returnDecision = CDD.TRUE;
			final RangeDecision d = (RangeDecision) decision;
			for (int i = 0; i < children.length; i++) {
				if (children[i] == CDD.FALSE) {
					continue;
				}
				if (dropOther) {
					returnDecision = returnDecision.and(upperToLowerBoundDecisionDropOther(d, i));
				} else {
					returnDecision = returnDecision.and(upperToLowerBoundDecision(d, i));
				}

			}
			return returnDecision;
		}
		return CDD.create(cdd.getDecision(), children);
	}

	private static CDD upperToLowerBoundDecision(final RangeDecision d, final int trueChild) {
		switch (d.getOp(trueChild)) {
		case RangeDecision.OP_LTEQ:
			return RangeDecision.create(d.getVar(), RangeDecision.OP_GTEQ, d.getVal(trueChild));
		default:
			return RangeDecision.create(d.getVar(), d.getOp(trueChild), d.getVal(trueChild));
		}
	}

	private static CDD upperToLowerBoundDecisionDropOther(final RangeDecision d, final int trueChild) {
		switch (d.getOp(trueChild)) {
		case RangeDecision.OP_LTEQ:
			return RangeDecision.create(d.getVar(), RangeDecision.OP_GTEQ, d.getVal(trueChild));
		default:
			return CDD.TRUE;
		}
	}

	public CDD transformGurad(final CDD cdd, final Set<String> effectVars, final Set<String> inputVars,
			final Set<String> constVars, final boolean isEffectEdge) {
		final Set<String> vars = getCddVariables(cdd);
		vars.removeAll(inputVars);
		vars.removeAll(constVars);
		if (isEffectEdge) {
			vars.removeAll(effectVars);
		}
		// TODO remove primed effect variables in a nicer way
		vars.removeAll(effectVars.stream().map(var -> var + "'").collect(Collectors.toSet()));
		vars.removeAll(inputVars.stream().map(var -> var + "'").collect(Collectors.toSet()));
		final CDD newGuard = addTrackingGuards(cdd, vars);
		return newGuard;
	}

	public static Set<String> getAllVariables(final PatternType<?> pattern) {
		final List<CounterTrace> cts = pattern.constructCounterTrace();
		final Set<String> variables = new HashSet<>();

		for (final CounterTrace ct : cts) {
			final DCPhase[] tc = ct.getPhases();
			// find max phase and second max phase, compare
			for (final DCPhase p : tc) {
				variables.addAll(getCddVariables(p.getInvariant()));
			}
		}
		return variables;
	}

	public static CDD getEffectCDD(final PatternType<?> pattern) {
		final List<CDD> cdds = pattern.getCdds();
		// lets just assume that the effect of the requirement is always mentioned at the end of the pattern (i.e. last
		// CDD)
		// e.g. it is always the case that if _condition_ then _effect_ holds for at least 5 (scope does not matter)
		// TODO: do not rely on this ordering and mark the effect in some way during parsing
		return cdds.get(0);
	}

	public static Set<String> getEffectVariables(final PatternType<?> pattern) {
		final List<CounterTrace> cts = pattern.constructCounterTrace();
		final Set<String> variables = new HashSet<>();

		for (final CounterTrace ct : cts) {
			final DCPhase[] tc = ct.getPhases();
			// find max phase and second max phase, compare
			final CDD finalStateInvar = tc[tc.length - 2].getInvariant();
			if (tc.length >= 3) {
				final CDD beforeStateInvar = tc[tc.length - 3].getInvariant();
				variables.addAll(getDifferences(beforeStateInvar, finalStateInvar));
			} else {
				variables.addAll(getCddVariables(finalStateInvar));
			}
		}
		return variables;
	}

	public static Set<String> getDifferences(final CDD beforeStateInvar, final CDD finalStateInvar) {
		final Set<String> differences = getCddVariables(finalStateInvar);
		// collect the atomics from both cdds
		final Set<CDD> beforeAtomics = getCDDAtoms(beforeStateInvar);
		for (final CDD cdd : finalStateInvar.toDNF()) {
			final Set<String> localDifferences = new HashSet<>();
			final Set<CDD> afterAtomics = getCDDAtoms(cdd);
			for (final CDD a : afterAtomics) {
				for (final CDD b : beforeAtomics) {
					if (a.isEqual(b)) {
						break;
					}
				}
				localDifferences.addAll(getVarsFromDecision(a.getDecision()));
			}
			differences.retainAll(localDifferences);
		}
		return differences;
	}

	private boolean hasDeterministicEffect(final CDD[] cdds, final Set<String> effectVars) {
		final Set<CDD> effectsPivoth = getEffectDecisions(cdds[0], effectVars);
		mLogger.warn("reference Effect: " + effectsPivoth);
		for (int i = 1; i < cdds.length; i++) {
			final Set<CDD> effects = getEffectDecisions(cdds[i], effectVars);
			if (!effects.isEmpty() && !effects.equals(effectsPivoth)) {
				mLogger.warn("non-det with Effect: " + getEffectDecisions(cdds[i], effectVars));
				return false;
			}
		}
		return true;
	}

	private static Set<CDD> getEffectDecisions(final CDD cdd, final Set<String> effectVars) {
		final Set<CDD> atomics = getCDDAtoms(cdd);
		final Set<CDD> effectAtoms = new HashSet<>();
		for (final CDD atom : atomics) {
			final Decision<?> d = atom.getDecision();
			if (d instanceof BoogieBooleanExpressionDecision) {
				for (final String var : effectVars) {
					if (((BoogieBooleanExpressionDecision) d).getVars().containsKey(var)) {
						effectAtoms.add(atom);
					}
				}
			}
		}
		return effectAtoms;
	}

	public static Set<CDD> getCDDAtoms(final CDD cdd) {
		final Set<CDD> atomics = new HashSet<>();
		extractAtomics(cdd, atomics);
		return atomics;
	}

	private static void extractAtomics(final CDD cdd, final Set<CDD> atomics) {
		if (cdd == CDD.TRUE || cdd == CDD.FALSE) {
			return;
		}
		if (cdd.isAtomic()) {
			atomics.add(cdd);
			return;
		}

		if (cdd.getChilds() != null) {
			for (final CDD child : cdd.getChilds()) {
				extractAtomics(child, atomics);
			}
		}
	}

	public static Set<String> getCddVariables(final CDD cdd) {
		final Set<String> variables = new HashSet<>();
		for (final Decision<?> dec : getDecisions(cdd)) {
			variables.addAll(getVarsFromDecision(dec));
		}
		return variables;
	}

	public static Set<String> getCddVariables(final Set<Decision<?>> cdds) {
		final Set<String> variables = new HashSet<>();
		for (final Decision<?> dec : cdds) {
			variables.addAll(getVarsFromDecision(dec));
		}
		return variables;
	}

	private static Set<String> getVarsFromDecision(final Decision<?> dec) {
		final Set<String> variables = new HashSet<>();
		if (dec == null) {
			// may happen for true/false phases
		} else if (dec instanceof EventDecision) {
			// requirements ignore events so far
		} else if (dec instanceof RangeDecision) {
			// range decisions are currently only used for clocks thus we ignore them here
		} else if (dec instanceof BooleanDecision) {
			variables.add(((BooleanDecision) dec).getVar());
		} else if (dec instanceof BoogieBooleanExpressionDecision) {
			final BoogieBooleanExpressionDecision bbedec = (BoogieBooleanExpressionDecision) dec;
			for (final Entry<String, String> entry : bbedec.getVars().entrySet()) {
				variables.add(entry.getKey());
			}
		} else {
			throw new UnsupportedOperationException("Unknown decision type: " + dec.getClass());
		}
		return variables;
	}

	public Map<String, String> getTrackingVars() {
		return mTrackingVars;
	}

	public static Set<Decision<?>> getDecisions(final CDD cdd) {
		final Set<Decision<?>> decisions = new HashSet<>();
		extractDecisions(cdd, decisions);
		return decisions;
	}

	private static void extractDecisions(final CDD cdd, final Set<Decision<?>> decisions) {
		if (cdd == CDD.TRUE || cdd == CDD.FALSE) {
			return;
		}
		decisions.add(cdd.getDecision());
		if (cdd.getChilds() != null) {
			for (final CDD child : cdd.getChilds()) {
				extractDecisions(child, decisions);
			}
		}
	}

}
