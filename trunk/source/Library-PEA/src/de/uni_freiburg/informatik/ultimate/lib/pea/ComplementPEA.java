package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;



/**
 * This class implements an algorithm for complementing Phase Event Automata as described in my bachelors thesis.
 * Documentation to be continued...
 *
 *aa
 * TODO: split Alg up in multiple methods
 *
 * @author Lena Funk
 */
public class ComplementPEA {
	
	PhaseEventAutomata mPEAtoComplement;
	
	PhaseEventAutomata mTotalisedPEA;
	
	PhaseEventAutomata mComplementPEA;
	
	
	public ComplementPEA(PhaseEventAutomata PEAtoComplement) {
		mPEAtoComplement = PEAtoComplement;	
		
		mTotalisedPEA = this.totalise();
		
		mComplementPEA = this.complement();
	}
	
	
	
	/**
	 * Totalised mPEAtoComplement
	 * 
	 * @return the Totalised PEA of mPEAtoComplement
	 */
	public PhaseEventAutomata totalise() {
		// create arrayList to collect phases for complement automaton
		List<Phase> phases = new ArrayList<>();
		// add sink with loop transition
		Phase sinkPhase = new Phase("sink", CDD.TRUE, CDD.TRUE);
		sinkPhase.addTransition(sinkPhase, CDD.TRUE, new String[] {});
		// for the Totalised PEA, the sink is not terminal
		sinkPhase.setTerminal(false);
		
		
		computeInitialTransitionSink(sinkPhase);
		phases.add(sinkPhase);
		
		// needed for priming/ unpriming
		Set<String> clockVarSet = new HashSet<>();
		clockVarSet.addAll(mPEAtoComplement.getClocks());
		
		for (Phase phase : mPEAtoComplement.getPhases()) {
			CDD clockInv = phase.getClockInvariant();
			CDD guardToSink = phase.stateInv.and(RangeDecision.strict(clockInv));
			Phase totalisedPhase = new Phase(phase.name, phase.stateInv, phase.clockInv);
			if (phase.getInitialTransition().isPresent()) {
				InitialTransition initialTransition = phase.getInitialTransition().get();
				InitialTransition newInitialTransition = new InitialTransition(initialTransition.getGuard(), totalisedPhase);
				totalisedPhase.setInitialTransition(newInitialTransition);
			}
			
			
			for (Transition transition : phase.transitions) {
				// add transition to new phase
				totalisedPhase.addTransition(transition.getDest(), transition.getGuard(), transition.getResets());
				String[] reset = transition.getResets();
				
				
				Phase successorPhase = transition.getDest();
				CDD successorStateInv = successorPhase.stateInv;
				CDD successorClockInv = successorPhase.clockInv;
				
				// compute guard to sink
				// we do not use the clock invariant of the successor phase
				// if the same clock is in the reset set of the transition
				CDD guardCdd = transition.getGuard();
				
				CDD guardUnprimed = guardCdd.unprime(clockVarSet);
				if (reset.length > 0) {
					CDD noResetClockInv = RangeDecision.filterCdd(successorClockInv, reset);					
					guardToSink = guardToSink.or(guardUnprimed.and(successorStateInv).and(RangeDecision.strict(noResetClockInv)));
				} else {
					guardToSink = guardToSink.or(guardUnprimed.and(successorStateInv).and(RangeDecision.strict(successorClockInv)));
				}
			}
			CDD guardToSinkPrimed = guardToSink.prime(clockVarSet);
			// make transition to sink 
			totalisedPhase.addTransition(sinkPhase, guardToSinkPrimed.negate(), new String[] {});
			
			
			// special case
			if (phase.isStrict()) {
				CDD totalisedClockInvariant = totalisedPhase.getClockInvariant();
				CDD strictClockInvariantDNF = totalisedClockInvariant.toDNF_CDD();
				List<RangeDecision> modifiedClockConstraints = new ArrayList<>();
				CDD nonStrictClockInvariant = strictConstraintHandling(strictClockInvariantDNF, CDD.TRUE, modifiedClockConstraints);
				
				totalisedPhase.setModifiedConstraints(modifiedClockConstraints);
				totalisedPhase.clockInv = nonStrictClockInvariant;

				for (Transition transition : totalisedPhase.transitions) {
					if (transition.getDest().getName() != "sink" ) {
						CDD modifiedGuard = transition.getGuard();
						for (RangeDecision clockConstraint : modifiedClockConstraints) {
							CDD clockConstraintCdd = RangeDecision.create(clockConstraint.getVar(), RangeDecision.OP_LT, clockConstraint.getVal(0));
							modifiedGuard = modifiedGuard.and(clockConstraintCdd);
						}
						transition.setGuard(modifiedGuard);
					}
				}
				
			}
			phases.add(totalisedPhase);
		}
		ArrayList<Phase> totalisedInit = new ArrayList<>(Arrays.asList(mPEAtoComplement.getInit()));
		if (sinkPhase.isInit) {
			totalisedInit.add(sinkPhase);
		}
		Phase[] totalisedInitArray = totalisedInit.toArray(new Phase[totalisedInit.size()]);
		PhaseEventAutomata totalisedPEA = new PhaseEventAutomata(mPEAtoComplement.getName() + "_t", phases.toArray(new Phase[phases.size()]), mPEAtoComplement.mInit);
		totalisedPEA.setInit(totalisedInitArray);
		totalisedPEA.mVariables = mPEAtoComplement.mVariables;
		totalisedPEA.mClocks = mPEAtoComplement.mClocks;
		return totalisedPEA;
	}
	
	/**
	 * Complements mPEAtoComplement
	 * 
	 * @return the complement automaton of mPEAtoComplement
	 */
	public PhaseEventAutomata complement() {
		List<Phase> phases = new ArrayList<>();
		for (Phase phase : mTotalisedPEA.getPhases()) {
			Phase complementPhase = new Phase(phase.name, phase.stateInv, phase.clockInv);
			boolean newTerminal = !phase.getTerminal();
			complementPhase.setTerminal(newTerminal);
			for (Transition transition : phase.transitions) {
				complementPhase.addTransition(transition.getDest(), transition.getGuard(), transition.getResets());
			}
			if (!phase.getInitialTransition().isEmpty()) {
				complementPhase.setInitialTransition(phase.getInitialTransition().get());
			}
			if (!phase.getModifiedConstraints().isEmpty()) {
				complementPhase.setModifiedConstraints(phase.getModifiedConstraints().get());
			}
			phases.add(complementPhase);
		}
		PhaseEventAutomata complementPEA = new PhaseEventAutomata(mPEAtoComplement.getName() + "_c", phases.toArray(new Phase[phases.size()]), mTotalisedPEA.mInit);
		complementPEA.mVariables = mPEAtoComplement.mVariables;
		complementPEA.mClocks = mPEAtoComplement.mClocks;
		return complementPEA;
	}
	

	/**
	 * Computes guard for initial transition to sink
	 * 
	 * @param sinkPhase
	 */
	private void computeInitialTransitionSink(Phase sinkPhase) {
		CDD initialTransitionSinkGuard = CDD.FALSE;
		Phase[] initialPhases = mPEAtoComplement.getInit();
		for (Phase phase : initialPhases) {
			assert phase.getInitialTransition().isPresent();
			InitialTransition initialTransition = phase.getInitialTransition().get();
			CDD conjunction = phase.getStateInvariant().and(initialTransition.getGuard());
			initialTransitionSinkGuard = initialTransitionSinkGuard.or(conjunction);
		}
		if (initialTransitionSinkGuard != CDD.TRUE) {
			InitialTransition sinkInitialTransition = new InitialTransition(initialTransitionSinkGuard.negate(), sinkPhase);
			sinkPhase.setInitialTransition(sinkInitialTransition);
		} else {
			sinkPhase.setInit(false);
		}
	}
	

	private CDD strictConstraintHandling(CDD clockInvariantDNF, CDD nonStrictClockInvariant, List<RangeDecision> strictClockConstraints) {
		if (clockInvariantDNF == CDD.TRUE || clockInvariantDNF == CDD.FALSE) {
			return nonStrictClockInvariant;
		}
		if (clockInvariantDNF.isAtomic()) {
			RangeDecision clockConstraint = (RangeDecision) clockInvariantDNF.getDecision();
			if (clockConstraint.getOp(0) == RangeDecision.OP_LT) {
				CDD nonStrictClockConstraint = RangeDecision.create(clockConstraint.getVar(), RangeDecision.OP_LTEQ, clockConstraint.getVal(0));
				nonStrictClockInvariant = nonStrictClockInvariant.and(nonStrictClockConstraint);
				strictClockConstraints.add(clockConstraint);
			} 
			return nonStrictClockInvariant;
		}

		if (clockInvariantDNF.getChilds() != null) {
			RangeDecision clockConstraint = (RangeDecision) clockInvariantDNF.getDecision();
			if (clockConstraint.getOp(0) == RangeDecision.OP_LT) {
				CDD nonStrictClockConstraint = RangeDecision.create(clockConstraint.getVar(), RangeDecision.OP_LTEQ, clockConstraint.getVal(0));
				nonStrictClockInvariant = nonStrictClockInvariant.and(nonStrictClockConstraint);
				strictClockConstraints.add(clockConstraint);
			}
			CDD trueChild = clockInvariantDNF.getChilds()[0];
			strictConstraintHandling(trueChild, nonStrictClockInvariant, strictClockConstraints);
		}
		return nonStrictClockInvariant;
	}
	
	public PhaseEventAutomata getTotalisedPEA() {
		return mTotalisedPEA;
	}
	
	public PhaseEventAutomata getComplementPEA() {
		return mComplementPEA;
	}
}
