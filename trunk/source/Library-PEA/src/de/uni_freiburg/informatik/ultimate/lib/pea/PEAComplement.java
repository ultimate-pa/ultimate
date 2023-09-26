package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class implements an algorithm for complementing Phase Event Automata as described in my bachelors thesis.
 * Documentation to be continued...
 *
 * TODO: split Alg up in multiple methods
 *
 * @author Lena Funk
 */
public class PEAComplement {

	public static String TOTAL_POSTFIX = "_total";
	public static String COMPLEMENT_POSTFIX = "_complement";

	final PhaseEventAutomata mPEAtoComplement;
	final PhaseEventAutomata mTotalisedPEA;
	final PhaseEventAutomata mComplementPEA;

	public PEAComplement(PhaseEventAutomata PEAtoComplement) {
		mPEAtoComplement = PEAtoComplement;
		mTotalisedPEA = this.totalise(mPEAtoComplement);
		mComplementPEA = this.complement(mTotalisedPEA);
	}

	/**
	 * Totalisation of input pea
	 * 
	 * @return the Totalised PEA of mPEAtoComplement
	 */
	public PhaseEventAutomata totalise(PhaseEventAutomata sourcePea) {
		// add sink with loop transition
		Phase sinkPhase = new Phase("sink", CDD.TRUE, CDD.TRUE);
		sinkPhase.addTransition(sinkPhase, CDD.TRUE, new String[] {});
		// for the Totalised PEA, the sink is not terminal
		sinkPhase.setTerminal(false);

		computeInitialTransitionSink(sourcePea, sinkPhase);
		final Map<String, Phase> totalisedPhases = copyPhases(sourcePea.getPhases(), TOTAL_POSTFIX);
		totalisedPhases.put(sinkPhase.name, sinkPhase);

		// prepare initial phases
		ArrayList<Phase> totalisedInit = new ArrayList<>();
		for (Phase p : sourcePea.getInit()) {
			totalisedInit.add(totalisedPhases.get(p.name));
		}
		if (sinkPhase.isInit) {
			totalisedInit.add(sinkPhase);
		}

		// needed for priming and unpriming
		Set<String> clockVarSet = new HashSet<>();
		clockVarSet.addAll(sourcePea.getClocks());

		for (Phase phase : sourcePea.getPhases()) {
			totalizeTransition(phase, sinkPhase, totalisedPhases, clockVarSet);
		}

		Phase[] totalisedInitArray = totalisedInit.toArray(new Phase[totalisedInit.size()]);
		PhaseEventAutomata totalisedPEA = new PhaseEventAutomata(sourcePea.getName() + TOTAL_POSTFIX,
				totalisedPhases.values().toArray(new Phase[totalisedPhases.size()]), sourcePea.mInit);
		totalisedPEA.setInit(totalisedInitArray);
		totalisedPEA.mVariables = new HashMap<String, String>(sourcePea.mVariables);

		for (String s : sourcePea.mClocks) {
			totalisedPEA.mClocks.add(s + TOTAL_POSTFIX);
		}
		return totalisedPEA;
	}

	private void totalizeTransition(Phase phase, Phase sinkPhase, Map<String, Phase> totalisedPhases,
			Set<String> clockVarSet) {
		Phase totalisedPhase = totalisedPhases.get(phase.name);
		CDD clockInv = phase.getClockInvariant();
		CDD guardToSink = phase.stateInv.and(RangeDecision.strict(clockInv));

		for (Transition transition : phase.transitions) {
			// add transition to new phase
			Phase totalisedSuccessor = totalisedPhases.get(transition.getDest().name);
			totalisedPhase.addTransition(totalisedSuccessor, addClockSuffixCDD(transition.getGuard(), TOTAL_POSTFIX),
					addClockSuffix(transition.getResets(), TOTAL_POSTFIX));
			String[] reset = transition.getResets();

			CDD successorStateInv = totalisedSuccessor.stateInv;
			CDD successorClockInv = totalisedSuccessor.clockInv;

			// compute guard to sink
			// we do not use the clock invariant of the successor phase
			// if the same clock is in the reset set of the transition
			CDD guardCdd = transition.getGuard();

			CDD guardUnprimed = guardCdd.unprime(clockVarSet);
			if (reset.length > 0) {
				CDD noResetClockInv = RangeDecision.filterCdd(successorClockInv, reset);
				guardToSink =
						guardToSink.or(guardUnprimed.and(successorStateInv).and(RangeDecision.strict(noResetClockInv)));
			} else {
				guardToSink = guardToSink
						.or(guardUnprimed.and(successorStateInv).and(RangeDecision.strict(successorClockInv)));
			}
		}
		CDD guardToSinkPrimed = guardToSink.prime(clockVarSet);
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
			totalisedPhase.clockInv = nonStrictClockInvariant;

			for (Transition transition : totalisedPhase.transitions) {
				if (transition.getDest().getName() != "sink") {
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
		totalisedPhases.put(totalisedPhase.name, totalisedPhase);
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
			Phase complementPhase = complementPhases.get(sourcePhase.name);
			boolean newTerminal = !sourcePhase.getTerminal();
			complementPhase.setTerminal(newTerminal);
			for (Transition transition : sourcePhase.transitions) {
				complementPhase.addTransition(complementPhases.get(transition.getDest().name),
						addClockSuffixCDD(transition.getGuard(), COMPLEMENT_POSTFIX),
						addClockSuffix(transition.getResets(), COMPLEMENT_POSTFIX));
			}
			// if (!complementPhase.getInitialTransition().isEmpty()) {
			// complementPhase.setInitialTransition(complementPhase.getInitialTransition().get());
			// }
			phases.add(complementPhase);
		}
		ArrayList<Phase> complementedInit = new ArrayList<>();
		for (Phase p : sourcePea.getInit()) {
			complementedInit.add(complementPhases.get(p.name));
		}
		Phase[] complementInitArray = complementedInit.toArray(new Phase[complementedInit.size()]);
		PhaseEventAutomata complementPEA = new PhaseEventAutomata(sourcePea.getName() + COMPLEMENT_POSTFIX,
				phases.toArray(new Phase[phases.size()]), complementInitArray);

		complementPEA.setInit(complementInitArray);
		complementPEA.mVariables = sourcePea.mVariables;
		complementPEA.mVariables = new HashMap<String, String>(sourcePea.mVariables);

		for (String s : sourcePea.getClocks()) {
			complementPEA.mClocks.add(s + COMPLEMENT_POSTFIX);
		}

		return complementPEA;
	}

	/**
	 * Computes guard for initial transition to sink
	 * 
	 * @param sinkPhase
	 */
	private void computeInitialTransitionSink(PhaseEventAutomata pea, Phase sinkPhase) {
		CDD initialTransitionSinkGuard = CDD.FALSE;
		Phase[] initialPhases = pea.getInit();
		for (Phase phase : initialPhases) {
			assert phase.getInitialTransition().isPresent();
			InitialTransition initialTransition = phase.getInitialTransition().get();
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

	private Map<String, Phase> copyPhases(Phase[] phases, String suffix) {
		Map<String, Phase> copy = new HashMap<String, Phase>();
		for (Phase phase : phases) {
			Phase copiedPhase = new Phase(phase.name, phase.stateInv, addClockSuffixCDD(phase.clockInv, suffix));
			copiedPhase.setTerminal(phase.getTerminal());
			copy.put(copiedPhase.name, copiedPhase);
			if (phase.getInitialTransition().isPresent()) {
				InitialTransition initialTransition = phase.getInitialTransition().get();
				InitialTransition newInitialTransition =
						new InitialTransition(initialTransition.getGuard(), copiedPhase);
				copiedPhase.setInitialTransition(newInitialTransition);
			}
			copiedPhase.setModifiedConstraints(phase.getModifiedConstraints());
		}
		return copy;
	}

	private String[] addClockSuffix(String[] clocks, String suffix) {
		ArrayList<String> clocksWithSuffix = new ArrayList<>();
		for (String clock : clocks) {
			String clockWithSuffix = clock + suffix;
			clocksWithSuffix.add(clockWithSuffix);
		}
		String[] clocksWithSuffixArray = new String[clocksWithSuffix.size()];
		return clocksWithSuffix.toArray(clocksWithSuffixArray);
	}

	@SuppressWarnings("unchecked")
	private CDD addClockSuffixCDD(CDD cdd, String suffix) {
		ArrayList<ArrayList<Pair<Decision<?>, int[]>>> dnfDecisions = cdd.getDecisionsDNF();
		ArrayList<CDD> conjunctionsWithSuffix = new ArrayList<>();
		for (ArrayList<Pair<Decision<?>, int[]>> conjunction : dnfDecisions) {
			CDD conjunctionWithSuffix = CDD.TRUE;
			for (Pair<Decision<?>, int[]> pair : conjunction) {
				if (pair.getFirst() instanceof RangeDecision) {
					Decision<RangeDecision> decision = (Decision<RangeDecision>) pair.getFirst();
					RangeDecision rangeDecision = (RangeDecision) decision;
					int trueChildIndex = pair.getSecond()[0];
					int op = rangeDecision.getOp(trueChildIndex);
					int value = rangeDecision.getVal(trueChildIndex);
					String clockVarWithSuffix = decision.getVar() + suffix;
					CDD rangeDecisionWithSuffix = RangeDecision.create(clockVarWithSuffix, op, value);
					conjunctionWithSuffix = conjunctionWithSuffix.and(rangeDecisionWithSuffix);
				} else { // boolean decision
					CDD booleanDecision = BooleanDecision.create(pair.getFirst().getVar());
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
