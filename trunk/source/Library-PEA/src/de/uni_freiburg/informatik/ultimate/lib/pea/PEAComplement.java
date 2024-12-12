/*
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE Regression Test Library.
 *
 * The ULTIMATE Regression Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Regression Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Regression Test Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Regression Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Regression Test Library grant you additional permission
 * to convey the resulting work.
 */
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
 * This class implements an algorithm for complementing Phase Event Automata as described in the bachelor thesis
 * "Complementation of Phase Event Automata" (L. Funk, 2023).
 *
 * @author Lena Funk
 */
public class PEAComplement {

	public static final String TOTAL_POSTFIX = "_total";
	public static final String COMPLEMENT_POSTFIX = "_complement";
	public static final String SINK_NAME = "sink";

	private final PhaseEventAutomata mPEAtoComplement;
	private final PhaseEventAutomata mTotalisedPEA;
	private final PhaseEventAutomata mComplementPEA;

	private final Set<String> mConstVars;

	public PEAComplement(final PhaseEventAutomata peaToComplement) {
		mPEAtoComplement = peaToComplement;
		mConstVars = Collections.emptySet();
		mTotalisedPEA = totalise(mPEAtoComplement);
		mComplementPEA = complement(mTotalisedPEA);
	}

	public PEAComplement(final PhaseEventAutomata peaToComplement, final Set<String> constVars) {
		mPEAtoComplement = peaToComplement;
		mConstVars = constVars;
		mTotalisedPEA = totalise(mPEAtoComplement);
		mComplementPEA = complement(mTotalisedPEA);
	}

	/**
	 * Totalisation of input pea. In a totalised PEA, each location has exactly one outgoing transition enabled for each
	 * valuation of variables and clock.
	 *
	 * @return the Totalised PEA of mPEAtoComplement
	 */
	public PhaseEventAutomata totalise(final PhaseEventAutomata sourcePea) {
		// add sink with loop transition
		final Phase sinkPhase = new Phase(SINK_NAME, CDD.TRUE, CDD.TRUE);
		sinkPhase.addTransition(sinkPhase, CDD.TRUE, new String[] {});
		// for the Totalised PEA, the sink is not terminal
		sinkPhase.setTerminal(false);

		computeInitialTransitionSink(sourcePea, sinkPhase);
		final Map<String, Phase> totalisedPhases = copyPhases(sourcePea.getPhases(), TOTAL_POSTFIX);
		totalisedPhases.put(sinkPhase.getName(), sinkPhase);

		// prepare initial phases
		final List<InitialTransition> totalisedInit = new ArrayList<>();
		for (final Phase p : sourcePea.getInit()) {
			totalisedInit.add(new InitialTransition(CDD.TRUE, totalisedPhases.get(p.getName())));
		}
		if (sinkPhase.isInit()) {
			totalisedInit.add(new InitialTransition(sinkPhase.getInitialTransition().getGuard(), sinkPhase));
		}

		// needed for priming and unpriming
		final Set<String> clockVarSet = new HashSet<>(sourcePea.getClocks());
		for (final Phase phase : sourcePea.getPhases()) {
			totalizeTransition(phase, sinkPhase, totalisedPhases, clockVarSet);
		}

		final List<String> newClocks = new ArrayList<>();
		for (final String s : sourcePea.getClocks()) {
			newClocks.add(addSuffixString(s, TOTAL_POSTFIX));
		}

		return new PhaseEventAutomata(addSuffixString(sourcePea.getName(), TOTAL_POSTFIX),
				new ArrayList<>(totalisedPhases.values()), totalisedInit, newClocks,
				new HashMap<>(sourcePea.getVariables()));
	}

	private void totalizeTransition(final Phase phase, final Phase sinkPhase, final Map<String, Phase> totalisedPhases,
			final Set<String> clockVarSet) {
		final Phase totalisedPhase = totalisedPhases.get(phase.getName());
		final CDD clockInv = phase.getClockInvariant();
		CDD guardToSink = phase.getStateInv().and(RangeDecision.strict(clockInv));

		// special case: PEAs with strict clock invariants. Clock invariants must be
		// non-strictified and guards of outgoing transitions must be modified to
		// explicitly contain the original clock invariant.
		if (phase.isStrict()) {
			final CDD totalisedClockInvariant = totalisedPhase.getClockInvariant();
			final CDD strictClockInvariantDNF = totalisedClockInvariant.toDNF_CDD();
			final List<RangeDecision> modifiedClockConstraints = new ArrayList<>();
			final CDD nonStrictClockInvariant = strictConstraintHandling(strictClockInvariantDNF, CDD.TRUE,
					modifiedClockConstraints);

			totalisedPhase.setModifiedConstraints(modifiedClockConstraints);
			totalisedPhase.setClockInv(nonStrictClockInvariant);

			for (final Transition transition : phase.getTransitions()) {
				CDD modifiedGuard = transition.getGuard();
				for (final RangeDecision clockConstraint : modifiedClockConstraints) {
					final CDD clockConstraintCdd = RangeDecision.create(clockConstraint.getVar(), RangeDecision.OP_LT,
							clockConstraint.getVal(0));
					modifiedGuard = modifiedGuard.and(clockConstraintCdd);
				}
				transition.setGuard(modifiedGuard);
			}

		}

		for (final Transition transition : phase.getTransitions()) {
			// add transition to new phase
			final Phase totalisedSuccessor = totalisedPhases.get(transition.getDest().getName());
			final Transition totalisedTransition = totalisedPhase.addTransition(totalisedSuccessor,
					addClockSuffixCDD(transition.getGuard(), TOTAL_POSTFIX),
					addClockSuffix(transition.getResets(), TOTAL_POSTFIX));
			final String[] reset = totalisedTransition.getResets();

			final CDD successorStateInv = totalisedSuccessor.getStateInv();
			final CDD successorClockInv = totalisedSuccessor.getClockInv();

			// compute guard to sink
			// we do not use the clock invariant of the successor phase
			// if the same clock is in the reset set of the transition
			final CDD guardCdd = transition.getGuard();

			final CDD guardUnprimed = guardCdd.unprime(clockVarSet);
			if (reset.length > 0) {
				final CDD noResetClockInv = RangeDecision.filterCdd(successorClockInv, reset);
				guardToSink =
						guardToSink.or(guardUnprimed.and(successorStateInv).and(RangeDecision.strict(noResetClockInv)));
			} else {
				guardToSink = guardToSink.or(guardUnprimed.and(successorStateInv)
						.and(RangeDecision.strict(successorClockInv)));
			}
		}
		final Set<String> unprimedVars = clockVarSet;
		unprimedVars.addAll(mConstVars);
		final CDD guardToSinkPrimed = guardToSink.prime(unprimedVars);
		final CDD guardToSinkWithClockSuffix = addClockSuffixCDD(guardToSinkPrimed, TOTAL_POSTFIX);
		// make transition to sink
		totalisedPhase.addTransition(sinkPhase, guardToSinkWithClockSuffix.negate(), new String[] {});
		totalisedPhases.put(totalisedPhase.getName(), totalisedPhase);
	}

	/**
	 * Complements a totalized PEA
	 *
	 * @return the complement automaton of mPEAtoComplement
	 */
	public PhaseEventAutomata complement(final PhaseEventAutomata sourcePea) {
		final List<Phase> phases = new ArrayList<>();
		final Map<String, Phase> complementPhases = copyPhases(sourcePea.mPhases, COMPLEMENT_POSTFIX);
		for (final Phase sourcePhase : sourcePea.getPhases()) {
			final Phase complementPhase = complementPhases.get(sourcePhase.getName());
			final boolean newTerminal = !sourcePhase.getTerminal();
			complementPhase.setTerminal(newTerminal);
			for (final Transition transition : sourcePhase.getTransitions()) {
				complementPhase.addTransition(complementPhases.get(transition.getDest().getName()),
						addClockSuffixCDD(transition.getGuard(), COMPLEMENT_POSTFIX),
						addClockSuffix(transition.getResets(), COMPLEMENT_POSTFIX));
			}
			phases.add(complementPhase);
		}
		final List<InitialTransition> complementedInit = new ArrayList<>();
		for (final Phase p : sourcePea.getInit()) {
			complementedInit
					.add(new InitialTransition(p.getInitialTransition().getGuard(), complementPhases.get(p.getName())));
		}

		final List<String> newClocks = new ArrayList<>();
		for (final String s : sourcePea.getClocks()) {
			newClocks.add(addSuffixString(s, TOTAL_POSTFIX));
		}

		return new PhaseEventAutomata(addSuffixString(sourcePea.getName(), COMPLEMENT_POSTFIX), phases,
				complementedInit, newClocks, new HashMap<>(sourcePea.getVariables()));
	}

	/**
	 * Computes guard for initial transition to sink
	 *
	 * @param sinkPhase
	 */
	private void computeInitialTransitionSink(final PhaseEventAutomata pea, final Phase sinkPhase) {
		CDD initialTransitionSinkGuard = CDD.FALSE;
		final List<Phase> initialPhases = pea.getInit();
		for (final Phase phase : initialPhases) {
			assert phase.getInitialTransition() != null;
			final InitialTransition initialTransition = phase.getInitialTransition();
			final CDD conjunction = phase.getStateInvariant().and(initialTransition.getGuard());
			initialTransitionSinkGuard = initialTransitionSinkGuard.or(conjunction);
		}
		if (initialTransitionSinkGuard != CDD.TRUE) {
			final InitialTransition sinkInitialTransition =
					new InitialTransition(initialTransitionSinkGuard.negate(), sinkPhase);
			sinkPhase.setInitialTransition(sinkInitialTransition);
		} else {
			sinkPhase.setInit(false);
		}
	}

	private CDD strictConstraintHandling(final CDD clockInvariantDNF, CDD nonStrictClockInvariant,
			final List<RangeDecision> strictClockConstraints) {
		if (clockInvariantDNF == CDD.TRUE || clockInvariantDNF == CDD.FALSE) {
			return nonStrictClockInvariant;
		}
		if (clockInvariantDNF.isAtomic()) {
			final RangeDecision clockConstraint = (RangeDecision) clockInvariantDNF.getDecision();
			if (clockConstraint.getOp(0) == RangeDecision.OP_LT) {
				final CDD nonStrictClockConstraint = RangeDecision.create(clockConstraint.getVar(),
						RangeDecision.OP_LTEQ, clockConstraint.getVal(0));
				nonStrictClockInvariant = nonStrictClockInvariant.and(nonStrictClockConstraint);
				strictClockConstraints.add(clockConstraint);
			}
			return nonStrictClockInvariant;
		}

		if (clockInvariantDNF.getChilds() != null) {
			final RangeDecision clockConstraint = (RangeDecision) clockInvariantDNF.getDecision();
			if (clockConstraint.getOp(0) == RangeDecision.OP_LT) {
				final CDD nonStrictClockConstraint = RangeDecision.create(clockConstraint.getVar(),
						RangeDecision.OP_LTEQ, clockConstraint.getVal(0));
				nonStrictClockInvariant = nonStrictClockInvariant.and(nonStrictClockConstraint);
				strictClockConstraints.add(clockConstraint);
			}
			final CDD trueChild = clockInvariantDNF.getChilds()[0];
			strictConstraintHandling(trueChild, nonStrictClockInvariant, strictClockConstraints);
		}
		return nonStrictClockInvariant;
	}

	private Map<String, Phase> copyPhases(final List<Phase> phases, final String suffix) {
		final Map<String, Phase> copy = new HashMap<>();
		for (final Phase phase : phases) {
			final Phase copiedPhase =
					new Phase(phase.getName(), phase.getStateInv(), addClockSuffixCDD(phase.getClockInv(), suffix));
			copiedPhase.setTerminal(phase.getTerminal());
			copy.put(copiedPhase.getName(), copiedPhase);
			if (phase.getInitialTransition() != null) {
				final InitialTransition initialTransition = phase.getInitialTransition();
				final InitialTransition newInitialTransition =
						new InitialTransition(initialTransition.getGuard(), copiedPhase);
				copiedPhase.setInitialTransition(newInitialTransition);
			}
			copiedPhase.setModifiedConstraints(phase.getModifiedConstraints());
		}
		return copy;
	}

	public String addSuffixString(final String varName, final String suffix) {
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

	private String[] addClockSuffix(final String[] clocks, final String suffix) {
		final List<String> clocksWithSuffix = new ArrayList<>();
		for (final String clock : clocks) {
			final String clockWithSuffix = addSuffixString(clock, suffix);
			clocksWithSuffix.add(clockWithSuffix);
		}
		final String[] clocksWithSuffixArray = new String[clocksWithSuffix.size()];
		return clocksWithSuffix.toArray(clocksWithSuffixArray);
	}

	@SuppressWarnings("unchecked")
	private CDD addClockSuffixCDD(final CDD cdd, final String suffix) {
		final List<List<Pair<Decision<?>, int[]>>> dnfDecisions = cdd.getDecisionsDNF();
		final List<CDD> conjunctionsWithSuffix = new ArrayList<>();
		for (final List<Pair<Decision<?>, int[]>> conjunction : dnfDecisions) {
			CDD conjunctionWithSuffix = CDD.TRUE;
			for (final Pair<Decision<?>, int[]> pair : conjunction) {
				if (pair.getFirst() instanceof RangeDecision) {
					final Decision<RangeDecision> decision = (Decision<RangeDecision>) pair.getFirst();
					final RangeDecision rangeDecision = (RangeDecision) decision;
					final int trueChildIndex = pair.getSecond()[0];
					final int op = rangeDecision.getOp(trueChildIndex);
					final int value = rangeDecision.getVal(trueChildIndex);
					final String clockVarWithSuffix = addSuffixString(decision.getVar(), suffix);
					final CDD rangeDecisionWithSuffix = RangeDecision.create(clockVarWithSuffix, op, value);
					conjunctionWithSuffix = conjunctionWithSuffix.and(rangeDecisionWithSuffix);
				} else if (pair.getFirst() instanceof BoogieBooleanExpressionDecision) {
					final BoogieBooleanExpressionDecision decision = (BoogieBooleanExpressionDecision) pair.getFirst();
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
		for (final CDD conjunction : conjunctionsWithSuffix) {
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