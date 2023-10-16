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

	public static String DIVIDER = "_";
	public static String TOTAL_POSTFIX = "_total";
	public static String COMPLEMENT_POSTFIX = "_complement";
	public static String SINK_NAME = "sink";

	final PhaseEventAutomata<CDD> mPEAtoComplement;
	final PhaseEventAutomata<CDD> mTotalisedPEA;
	final PhaseEventAutomata<CDD> mComplementPEA;

	public PEAComplement(PhaseEventAutomata<CDD> PEAtoComplement) {
		mPEAtoComplement = PEAtoComplement;
		mTotalisedPEA = this.totalise(mPEAtoComplement);
		mComplementPEA = this.complement(mTotalisedPEA);
	}

	/**
	 * Totalisation of input pea
	 * 
	 * @return the Totalised PEA of mPEAtoComplement
	 */
	public PhaseEventAutomata<CDD> totalise(PhaseEventAutomata<CDD> sourcePea) {
		// add sink with loop transition
		Phase<CDD> sinkPhase = new Phase<CDD>(SINK_NAME, CDD.TRUE, CDD.TRUE);
		sinkPhase.addTransition(sinkPhase, CDD.TRUE, new String[] {});
		// for the Totalised PEA, the sink is not terminal
		sinkPhase.setTerminal(false);

		computeInitialTransitionSink(sourcePea, sinkPhase);
		final Map<String, Phase<CDD>> totalisedPhases = copyPhases(sourcePea.getPhases(), TOTAL_POSTFIX);
		totalisedPhases.put(sinkPhase.name, sinkPhase);

		// prepare initial phases
		ArrayList<InitialTransition<CDD>> totalisedInit = new ArrayList<>();
		for (Phase<CDD> p : sourcePea.getInit()) {
			totalisedInit.add(new InitialTransition<CDD>(CDD.TRUE, totalisedPhases.get(p.name)));
		}
		if (sinkPhase.isInit) {
			totalisedInit.add(new InitialTransition<CDD>(sinkPhase.mInitialTransition.getGuard(), sinkPhase));
		}

		// needed for priming and unpriming
		Set<String> clockVarSet = new HashSet<>();
		clockVarSet.addAll(sourcePea.getClocks());

		for (Phase<CDD> phase : sourcePea.getPhases()) {
			totalizeTransition(phase, sinkPhase, totalisedPhases, clockVarSet);
		}

		PhaseEventAutomata<CDD> totalisedPEA =
				new PhaseEventAutomata<CDD>(addSuffixString(sourcePea.getName(), TOTAL_POSTFIX),
						new ArrayList<Phase<CDD>>(totalisedPhases.values()), totalisedInit);
		totalisedPEA.mVariables = new HashMap<String, String>(sourcePea.mVariables);

		for (String s : sourcePea.mClocks) {
			totalisedPEA.mClocks.add(addSuffixString(s, TOTAL_POSTFIX));
		}
		return totalisedPEA;
	}

	private void totalizeTransition(Phase<CDD> phase, Phase<CDD> sinkPhase, Map<String, Phase<CDD>> totalisedPhases,
			Set<String> clockVarSet) {
		Phase<CDD> totalisedPhase = totalisedPhases.get(phase.name);
		CDD clockInv = phase.getClockInvariant();
		CDD guardToSink = phase.stateInv.and(RangeDecision.strict(clockInv));

		for (Transition<CDD> transition : phase.transitions) {
			// add transition to new phase
			Phase<CDD> totalisedSuccessor = totalisedPhases.get(transition.getDest().name);
			Transition totalisedTransition = totalisedPhase.addTransition(totalisedSuccessor,
					addClockSuffixCDD(transition.getGuard(), TOTAL_POSTFIX),
					addClockSuffix(transition.getResets(), TOTAL_POSTFIX));
			String[] reset = totalisedTransition.getResets();

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

			for (Transition<CDD> transition : totalisedPhase.transitions) {
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
		totalisedPhases.put(totalisedPhase.name, totalisedPhase);
	}

	/**
	 * Complements a totalized PEA
	 * 
	 * @return the complement automaton of mPEAtoComplement
	 */
	public PhaseEventAutomata<CDD> complement(PhaseEventAutomata<CDD> sourcePea) {
		List<Phase<CDD>> phases = new ArrayList<>();
		Map<String, Phase<CDD>> complementPhases = copyPhases(sourcePea.mPhases, COMPLEMENT_POSTFIX);
		for (Phase<CDD> sourcePhase : sourcePea.getPhases()) {
			Phase<CDD> complementPhase = complementPhases.get(sourcePhase.name);
			boolean newTerminal = !sourcePhase.getTerminal();
			complementPhase.setTerminal(newTerminal);
			for (Transition<CDD> transition : sourcePhase.transitions) {
				complementPhase.addTransition(complementPhases.get(transition.getDest().name),
						addClockSuffixCDD(transition.getGuard(), COMPLEMENT_POSTFIX),
						addClockSuffix(transition.getResets(), COMPLEMENT_POSTFIX));
			}
			phases.add(complementPhase);
		}
		ArrayList<InitialTransition<CDD>> complementedInit = new ArrayList<>();
		for (Phase<CDD> p : sourcePea.getInit()) {
			complementedInit
					.add(new InitialTransition<CDD>(p.mInitialTransition.getGuard(), complementPhases.get(p.name)));
		}
		PhaseEventAutomata<CDD> complementPEA = new PhaseEventAutomata<CDD>(
				addSuffixString(sourcePea.getName(), COMPLEMENT_POSTFIX), phases, complementedInit);

		complementPEA.mVariables = sourcePea.mVariables;
		complementPEA.mVariables = new HashMap<String, String>(sourcePea.mVariables);

		for (String s : sourcePea.getClocks()) {
			complementPEA.mClocks.add(addSuffixString(s, COMPLEMENT_POSTFIX));
		}

		return complementPEA;
	}

	/**
	 * Computes guard for initial transition to sink
	 * 
	 * @param sinkPhase
	 */
	private void computeInitialTransitionSink(PhaseEventAutomata<CDD> pea, Phase<CDD> sinkPhase) {
		CDD initialTransitionSinkGuard = CDD.FALSE;
		List<Phase<CDD>> initialPhases = pea.getInit();
		for (Phase<CDD> phase : initialPhases) {
			assert phase.getInitialTransition() != null;
			InitialTransition<CDD> initialTransition = phase.getInitialTransition();
			CDD conjunction = phase.getStateInvariant().and(initialTransition.getGuard());
			initialTransitionSinkGuard = initialTransitionSinkGuard.or(conjunction);
		}
		if (initialTransitionSinkGuard != CDD.TRUE) {
			InitialTransition<CDD> sinkInitialTransition =
					new InitialTransition<CDD>(initialTransitionSinkGuard.negate(), sinkPhase);
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

	private Map<String, Phase<CDD>> copyPhases(List<Phase<CDD>> phases, String suffix) {
		Map<String, Phase<CDD>> copy = new HashMap<String, Phase<CDD>>();
		for (Phase<CDD> phase : phases) {
			Phase<CDD> copiedPhase =
					new Phase<CDD>(phase.name, phase.stateInv, addClockSuffixCDD(phase.clockInv, suffix));
			copiedPhase.setTerminal(phase.getTerminal());
			copy.put(copiedPhase.name, copiedPhase);
			if (phase.getInitialTransition() != null) {
				InitialTransition<CDD> initialTransition = phase.getInitialTransition();
				InitialTransition<CDD> newInitialTransition =
						new InitialTransition<CDD>(initialTransition.getGuard(), copiedPhase);
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
					String clockVarWithSuffix = addSuffixString(decision.getVar(), suffix);
					CDD rangeDecisionWithSuffix = RangeDecision.create(clockVarWithSuffix, op, value);
					conjunctionWithSuffix = conjunctionWithSuffix.and(rangeDecisionWithSuffix);
				} else if (pair.getFirst() instanceof BoogieBooleanExpressionDecision) {
					BoogieBooleanExpressionDecision decision = (BoogieBooleanExpressionDecision) pair.getFirst();
					CDD booleanDecision = BoogieBooleanExpressionDecision.create(decision.getExpression());
					if (pair.getSecond()[0] == 1) { // when the index of the true child is 1, the decision is negated
						booleanDecision = booleanDecision.negate();
					}
				} else { // boolean decision
					Decision<BooleanDecision> decision = (Decision<BooleanDecision>) pair.getFirst();
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

	public PhaseEventAutomata<CDD> getTotalisedPEA() {
		return mTotalisedPEA;
	}

	public PhaseEventAutomata<CDD> getComplementPEA() {
		return mComplementPEA;
	}

}
