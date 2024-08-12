package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class implements an algorithm for complementing Phase Event Automata as
 * described in the bachelor thesis "Complementation of Phase Event Automata"
 * (L. Funk, 2023).
 *
 * @author Lena Funk
 */
public class PEAComplement {

	public static String TOTAL_POSTFIX = "_total";
	public static String COMPLEMENT_POSTFIX = "_complement";
	public static String SINK_NAME = "sink";

	final PhaseEventAutomata mPEAtoComplement;
	final PhaseEventAutomata mTotalisedPEA;
	final PhaseEventAutomata mComplementPEA;

	private static Set<String> mConstVars;

	public PEAComplement(PhaseEventAutomata peaToComplement) {
		mPEAtoComplement = peaToComplement;
		mConstVars = Collections.emptySet();
		mTotalisedPEA = totalise(mPEAtoComplement);
		mComplementPEA = complement(mTotalisedPEA);
	}

	public PEAComplement(PhaseEventAutomata peaToComplement, Set<String> constVars) {
		mPEAtoComplement = peaToComplement;
		mConstVars = constVars;
		mTotalisedPEA = totalise(mPEAtoComplement);
		mComplementPEA = complement(mTotalisedPEA);
	}

	/**
	 * Totalisation of input pea. In a totalised PEA, each location has exactly one
	 * outgoing transition enabled for each valuation of variables and clock.
	 * 
	 * @return the Totalised PEA of mPEAtoComplement
	 */
	public PhaseEventAutomata totalise(PhaseEventAutomata sourcePea) {
		// add sink with loop transition
		Phase sinkPhase = new Phase(SINK_NAME, CDD.TRUE, CDD.TRUE);
		sinkPhase.addTransition(sinkPhase, CDD.TRUE, new String[] {});
		// for the Totalised PEA, the sink is not terminal
		sinkPhase.setTerminal(false);

		computeInitialTransitionSink(sourcePea, sinkPhase);
		final Map<String, Phase> totalisedPhases = copyPhases(sourcePea.getPhases(), TOTAL_POSTFIX);
		totalisedPhases.put(sinkPhase.getName(), sinkPhase);

		// prepare initial phases
		ArrayList<InitialTransition> totalisedInit = new ArrayList<>();
		for (Phase p : sourcePea.getInit()) {
			totalisedInit.add(new InitialTransition(CDD.TRUE, totalisedPhases.get(p.getName())));
		}
		if (sinkPhase.isInit) {
			totalisedInit.add(new InitialTransition(sinkPhase.getInitialTransition().getGuard(), sinkPhase));
		}

		// needed for priming and unpriming
		Set<String> clockVarSet = new HashSet<>();
		clockVarSet.addAll(sourcePea.getClocks());

		for (Phase phase : sourcePea.getPhases()) {
			totalizeTransition(phase, sinkPhase, totalisedPhases, clockVarSet);
		}

		final List<String> newClocks = new ArrayList<>();
		for (String s : sourcePea.getClocks()) {
			newClocks.add(addSuffixString(s, TOTAL_POSTFIX));
		}

		PhaseEventAutomata totalisedPEA = new PhaseEventAutomata(addSuffixString(sourcePea.getName(), TOTAL_POSTFIX),
				new ArrayList<Phase>(totalisedPhases.values()), totalisedInit, newClocks,
				new HashMap<String, String>(sourcePea.getVariables()));

		return totalisedPEA;
	}

	private void totalizeTransition(Phase phase, Phase sinkPhase, Map<String, Phase> totalisedPhases,
			Set<String> clockVarSet) {
		Phase totalisedPhase = totalisedPhases.get(phase.getName());
		CDD clockInv = phase.getClockInvariant();
		CDD guardToSink = phase.getStateInv().and(RangeDecision.strict(clockInv));

		for (Transition transition : phase.getTransitions()) {
			// add transition to new phase
			Phase totalisedSuccessor = totalisedPhases.get(transition.getDest().getName());
			Transition totalisedTransition = totalisedPhase.addTransition(totalisedSuccessor,
					addClockSuffixCDD(transition.getGuard(), TOTAL_POSTFIX),
					addClockSuffix(transition.getResets(), TOTAL_POSTFIX));
			String[] reset = totalisedTransition.getResets();

			CDD successorStateInv = totalisedSuccessor.getStateInv();
			CDD successorClockInv = totalisedSuccessor.getClockInv();

			// compute guard to sink
			// we do not use the clock invariant of the successor phase
			// if the same clock is in the reset set of the transition
			CDD guardCdd = transition.getGuard();

			CDD guardUnprimed = guardCdd.unprime(clockVarSet);
			if (reset.length > 0) {
				CDD noResetClockInv = RangeDecision.filterCdd(successorClockInv, reset);
				guardToSink =
						guardToSink.or(guardUnprimed.and(successorStateInv).and(RangeDecision.strict(noResetClockInv)))
								.and(RangeDecision.strict(clockInv));
			} else {
				guardToSink = guardToSink.or(guardUnprimed.and(successorStateInv)
						.and(RangeDecision.strict(successorClockInv)).and(clockInv));
			}
		}
		Set<String> unprimedVars = clockVarSet;
		unprimedVars.addAll(mConstVars);
		CDD guardToSinkPrimed = guardToSink.prime(unprimedVars);
		CDD guardToSinkWithClockSuffix = addClockSuffixCDD(guardToSinkPrimed, TOTAL_POSTFIX);
		// make transition to sink
		totalisedPhase.addTransition(sinkPhase, guardToSinkWithClockSuffix.negate(), new String[] {});

		// special case
		if (phase.isStrict()) {
			CDD totalisedClockInvariant = totalisedPhase.getClockInvariant();
			CDD strictClockInvariantDNF = totalisedClockInvariant.toDNF_CDD();
			List<RangeDecision> modifiedClockConstraints = new ArrayList<>();
			CDD nonStrictClockInvariant =
					strictConstraintHandling(strictClockInvariantDNF, CDD.TRUE, modifiedClockConstraints);

			totalisedPhase.setModifiedConstraints(modifiedClockConstraints);
			totalisedPhase.setClockInv(nonStrictClockInvariant);

			for (Transition transition : totalisedPhase.getTransitions()) {
				if (transition.getDest().getName() != SINK_NAME) {
					CDD modifiedGuard = transition.getGuard();
					for (RangeDecision clockConstraint : modifiedClockConstraints) {
						CDD clockConstraintCdd = RangeDecision.create(clockConstraint.getVar(), RangeDecision.OP_LT,
								clockConstraint.getVal(0));
						modifiedGuard = modifiedGuard.and(clockConstraintCdd);
					}
					transition.setGuard(modifiedGuard);
				}
			}

		}
		totalisedPhases.put(totalisedPhase.getName(), totalisedPhase);
	}

	/**
	 * Complements a totalized PEA
	 * 
	 * @return the complement automaton of mPEAtoComplement
	 */
	public PhaseEventAutomata complement(PhaseEventAutomata sourcePea) {
		List<Phase> phases = new ArrayList<>();
		Map<String, Phase> complementPhases = copyPhases(sourcePea.mPhases, COMPLEMENT_POSTFIX);
		for (Phase sourcePhase : sourcePea.getPhases()) {
			Phase complementPhase = complementPhases.get(sourcePhase.getName());
			boolean newTerminal = !sourcePhase.getTerminal();
			complementPhase.setTerminal(newTerminal);
			for (Transition transition : sourcePhase.getTransitions()) {
				complementPhase.addTransition(complementPhases.get(transition.getDest().getName()),
						addClockSuffixCDD(transition.getGuard(), COMPLEMENT_POSTFIX),
						addClockSuffix(transition.getResets(), COMPLEMENT_POSTFIX));
			}
			phases.add(complementPhase);
		}
		ArrayList<InitialTransition> complementedInit = new ArrayList<>();
		for (Phase p : sourcePea.getInit()) {
			complementedInit
					.add(new InitialTransition(p.getInitialTransition().getGuard(), complementPhases.get(p.getName())));
		}

		final List<String> newClocks = new ArrayList<>();
		for (String s : sourcePea.getClocks()) {
			newClocks.add(addSuffixString(s, TOTAL_POSTFIX));
		}

		PhaseEventAutomata complementPEA =
				new PhaseEventAutomata(addSuffixString(sourcePea.getName(), COMPLEMENT_POSTFIX), phases,
						complementedInit, newClocks, new HashMap<String, String>(sourcePea.getVariables()));

		return complementPEA;
	}

	/**
	 * Computes guard for initial transition to sink
	 * 
	 * @param sinkPhase
	 */
	private void computeInitialTransitionSink(PhaseEventAutomata pea, Phase sinkPhase) {
		CDD initialTransitionSinkGuard = CDD.FALSE;
		List<Phase> initialPhases = pea.getInit();
		for (Phase phase : initialPhases) {
			assert phase.getInitialTransition() != null;
			InitialTransition initialTransition = phase.getInitialTransition();
			CDD conjunction = phase.getStateInvariant().and(initialTransition.getGuard());
			initialTransitionSinkGuard = initialTransitionSinkGuard.or(conjunction);
		}
		if (initialTransitionSinkGuard != CDD.TRUE) {
			InitialTransition sinkInitialTransition =
					new InitialTransition(initialTransitionSinkGuard.negate(), sinkPhase);
			sinkPhase.setInitialTransition(sinkInitialTransition);
		} else {
			sinkPhase.setInit(false);
		}
	}

	private CDD strictConstraintHandling(CDD clockInvariantDNF, CDD nonStrictClockInvariant,
			List<RangeDecision> strictClockConstraints) {
		if (clockInvariantDNF == CDD.TRUE || clockInvariantDNF == CDD.FALSE) {
			return nonStrictClockInvariant;
		}
		if (clockInvariantDNF.isAtomic()) {
			RangeDecision clockConstraint = (RangeDecision) clockInvariantDNF.getDecision();
			if (clockConstraint.getOp(0) == RangeDecision.OP_LT) {
				CDD nonStrictClockConstraint = RangeDecision.create(clockConstraint.getVar(), RangeDecision.OP_LTEQ,
						clockConstraint.getVal(0));
				nonStrictClockInvariant = nonStrictClockInvariant.and(nonStrictClockConstraint);
				strictClockConstraints.add(clockConstraint);
			}
			return nonStrictClockInvariant;
		}

		if (clockInvariantDNF.getChilds() != null) {
			RangeDecision clockConstraint = (RangeDecision) clockInvariantDNF.getDecision();
			if (clockConstraint.getOp(0) == RangeDecision.OP_LT) {
				CDD nonStrictClockConstraint = RangeDecision.create(clockConstraint.getVar(), RangeDecision.OP_LTEQ,
						clockConstraint.getVal(0));
				nonStrictClockInvariant = nonStrictClockInvariant.and(nonStrictClockConstraint);
				strictClockConstraints.add(clockConstraint);
			}
			CDD trueChild = clockInvariantDNF.getChilds()[0];
			strictConstraintHandling(trueChild, nonStrictClockInvariant, strictClockConstraints);
		}
		return nonStrictClockInvariant;
	}

	private Map<String, Phase> copyPhases(List<Phase> phases, String suffix) {
		Map<String, Phase> copy = new HashMap<String, Phase>();
		for (Phase phase : phases) {
			Phase copiedPhase =
					new Phase(phase.getName(), phase.getStateInv(), addClockSuffixCDD(phase.getClockInv(), suffix));
			copiedPhase.setTerminal(phase.getTerminal());
			copy.put(copiedPhase.getName(), copiedPhase);
			if (phase.getInitialTransition() != null) {
				InitialTransition initialTransition = phase.getInitialTransition();
				InitialTransition newInitialTransition =
						new InitialTransition(initialTransition.getGuard(), copiedPhase);
				copiedPhase.setInitialTransition(newInitialTransition);
			}
			copiedPhase.setModifiedConstraints(phase.getModifiedConstraints());
		}
		return copy;
	}

	public String addSuffixString(String varName, String suffix) {
		String stringWithSuffix;
		if (varName.contains(COMPLEMENT_POSTFIX)) {
			stringWithSuffix = varName.split(COMPLEMENT_POSTFIX)[0];
			stringWithSuffix = stringWithSuffix + suffix;
		}
		if (varName.contains(TOTAL_POSTFIX)) {
			stringWithSuffix = varName.split(TOTAL_POSTFIX)[0];
			stringWithSuffix = stringWithSuffix + suffix;
		} else {
			stringWithSuffix = varName + suffix;
		}
		return stringWithSuffix;
	}

	private String[] addClockSuffix(String[] clocks, String suffix) {
		ArrayList<String> clocksWithSuffix = new ArrayList<>();
		for (String clock : clocks) {
			String clockWithSuffix = addSuffixString(clock, suffix);
			clocksWithSuffix.add(clockWithSuffix);
		}
		String[] clocksWithSuffixArray = new String[clocksWithSuffix.size()];
		return clocksWithSuffix.toArray(clocksWithSuffixArray);
	}

	@SuppressWarnings("unchecked")
	private CDD addClockSuffixCDD(CDD cdd, String suffix) {
		List<List<Pair<Decision<?>, int[]>>> dnfDecisions = cdd.getDecisionsDNF();
		ArrayList<CDD> conjunctionsWithSuffix = new ArrayList<>();
		for (List<Pair<Decision<?>, int[]>> conjunction : dnfDecisions) {
			CDD conjunctionWithSuffix = CDD.TRUE;
			for (Pair<Decision<?>, int[]> pair : conjunction) {
				if (pair.getFirst() instanceof RangeDecision) {
					Decision<RangeDecision> decision = (Decision<RangeDecision>) pair.getFirst();
					RangeDecision rangeDecision = (RangeDecision) decision;
					int trueChildIndex = pair.getSecond()[0];
					int op = rangeDecision.getOp(trueChildIndex);
					int value = rangeDecision.getVal(trueChildIndex);
					String clockVarWithSuffix = addSuffixString(decision.getVar(), suffix);
					CDD rangeDecisionWithSuffix = RangeDecision.create(clockVarWithSuffix, op, value);
					conjunctionWithSuffix = conjunctionWithSuffix.and(rangeDecisionWithSuffix);
				} else if (pair.getFirst() instanceof BoogieBooleanExpressionDecision) {
					BoogieBooleanExpressionDecision decision = (BoogieBooleanExpressionDecision) pair.getFirst();
					CDD booleanDecision = BoogieBooleanExpressionDecision.create(decision.getExpression());
					if (pair.getSecond()[0] == 1) { // when the index of the true child is 1, the decision is negated
						booleanDecision = booleanDecision.negate();
					}
					conjunctionWithSuffix = conjunctionWithSuffix.and(booleanDecision);
				} else { // boolean decision
					CDD booleanDecision = BooleanDecision.create(pair.getFirst().getVar());
					if (pair.getSecond()[0] == 1) { // when the index of the true child is 1, the decision is negated
						booleanDecision = booleanDecision.negate();
					}
					conjunctionWithSuffix = conjunctionWithSuffix.and(booleanDecision);
				}
			}
			conjunctionsWithSuffix.add(conjunctionWithSuffix);
		}
		CDD disjunctionWithSuffix = CDD.FALSE;
		for (CDD conjunction : conjunctionsWithSuffix) {
			disjunctionWithSuffix = disjunctionWithSuffix.or(conjunction);
		}
		return disjunctionWithSuffix;
	}

	public PhaseEventAutomata getTotalisedPEA() {
		return mTotalisedPEA;
	}

	public PhaseEventAutomata getComplementPEA() {
		return mComplementPEA;
	}

}