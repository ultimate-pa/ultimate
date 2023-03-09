package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.awt.geom.CubicCurve2D;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;


/**
 * This class implements an algorithm for complementing Phase Event Automata as described in my bachelors thesis.
 * To be continued...
 *
 * @author Lena Funk
 */
public class ComplementPEA {
	
	PhaseEventAutomata mPEAtoComplement;
	
	
	public ComplementPEA(PhaseEventAutomata PEAtoComplement) {
		mPEAtoComplement = PEAtoComplement;		
	}
	
	
	/**
	 * Complements mPEAtoComplement
	 * 
	 * @return the complement automaton of mPEAtoComplement
	 */
	public PhaseEventAutomata complement() {
		// create arrayList to collect phases for complement automaton
		List<Phase> phases = new ArrayList<>();
		
		// add sink with loop transition
		Phase sinkPhase = new Phase("sink", CDD.TRUE, CDD.TRUE);
		sinkPhase.addTransition(sinkPhase, CDD.TRUE, new String[] {});
		phases.add(sinkPhase);
		
		// TODO: 
		// compute guard for initial transition to sink
		// set sink as initial phase 
		
		for (Phase phase : mPEAtoComplement.getPhases()) {
			CDD clockInv = phase.getClockInvariant();
			Decision<?> clockDecision = clockInv.getDecision();
			CDD guardToSink = phase.stateInv.and(RangeDecision.strict(clockInv));
			// create new phase for complement automaton that is not accepting
			Phase newPhase = new Phase(phase.name, phase.stateInv, phase.clockInv);
			newPhase.setAccepting(false);
			
			
			for (Transition transition : phase.transitions) {
				// add transition to new phase
				newPhase.addTransition(transition.getDest(), transition.getGuard(), transition.getResets());
				String[] reset = transition.getResets();
				
				
				Phase successorPhase = transition.getDest();
				CDD successorStateInv = successorPhase.stateInv;
				CDD successorClockInv = successorPhase.clockInv;
				
				// compute guard to sink
				// we do not use the clock invariant of the successor phase
				// if the same clock is in the reset set of the transition
				CDD noResetCdd = CDD.TRUE;
				CDD strictCdd = CDD.TRUE;
				if (reset.length > 0) {
					CDD noResetClockInv = RangeDecision.filterCdd(successorClockInv, reset);
							//noReset(successorClockInv, reset, noResetCdd);
					guardToSink = guardToSink.or(transition.getGuard().and(successorStateInv).and(RangeDecision.strict(noResetClockInv)));
				} else {
					guardToSink = guardToSink.or(transition.getGuard().and(successorStateInv).and(RangeDecision.strict(successorClockInv)));
				}
			}
			// make transition to sink 
			newPhase.addTransition(sinkPhase, guardToSink.negate(), new String[] {});
			phases.add(newPhase);
			
			Decision<?> clockDecision = newPhase.getClockInvariant().getDecision();
			
			// special case: clock invariant is  c < T
			if (clockDecision instanceof RangeDecision) {
				// make clock invariant non-strict
				RangeDecision clockInv = (RangeDecision) clockDecision;
				// int numChilds = newPhase.getClockInvariant().getChilds().length;
				if (clockInv.getOp(0) == RangeDecision.OP_LT) {
					newPhase.clockInv = RangeDecision.create(clockInv.getVar(), RangeDecision.OP_LTEQ, clockInv.getVal(0));
				}
				// add c < T as guard to all outgoing transitions
				// TODO: correct? 
				for (Transition transition : newPhase.transitions) {
					CDD newGuard = transition.getGuard().and(RangeDecision.create(clockInv.getVar(), RangeDecision.OP_LT, clockInv.getVal(0)));
					transition.setGuard(newGuard);
				}
			}
		}
		PhaseEventAutomata complementedPEA = new PhaseEventAutomata("aaaaa",  phases.toArray(new Phase[0]), mPEAtoComplement.mInit);
		return complementedPEA;
	}
}
