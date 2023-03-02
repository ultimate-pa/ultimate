package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.security.PublicKey;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

// TODO: Soll man Phasen nochmal neu machen oder kann man die vom alten PEA nehmen? Die haben eine ID.

/**
 * This class implements an algorithm for complementing Phase Event Automata. 
 *
 * @author Lena Funk
 *
 */
public class ComplementPEA {
	
	PhaseEventAutomata mPEAtoComplement;
	
	
	public ComplementPEA(PhaseEventAutomata PEAtoComplement) {
		mPEAtoComplement = PEAtoComplement;
		
		
	}
	
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
			CDD guardToSink = phase.stateInv.and(strict(phase.clockInv));
			// create new phase for complement automaton that is not accepting
			Phase newPhase = new Phase(phase.name, phase.stateInv, phase.clockInv);
			newPhase.setAccepting(false);
			
			
			for (Transition transition : phase.transitions) {
				// add transition to new phase
				newPhase.addTransition(transition.getDest(), transition.getGuard(), transition.getResets());
				String[] reset = transition.getResets();
				
				// compute guard to sink
				Phase successorPhase = transition.getDest();
				CDD successorStateInv = successorPhase.stateInv;
				CDD successorClockInv = successorPhase.clockInv;
				RangeDecision clockInvDecision = null;
				
				// we do not use the clock invariant of the successor phase
				// if the same clock is in the reset set of the transition
				// TODO: what if a clock invariant refers to multiple clock variables
				// and not all of them are in the reset set?
				String clock = "none";
				if ( successorClockInv.getDecision() instanceof RangeDecision) {
					clockInvDecision = (RangeDecision) successorClockInv.getDecision() ;
					clock =  clockInvDecision.getVar();
					
				}
				
				// if the clock  of the clock invariant gets reset, 
				// the clock invariant does not need to be in the guard
				if (Arrays.asList(reset).contains(clock)) {
					guardToSink = guardToSink.or(transition.getGuard().and(successorStateInv));
				} else {
					guardToSink = guardToSink.or(transition.getGuard().and(successorStateInv).and(strict(successorClockInv)));
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
	
	public CDD strict(CDD clockInv) {
		Decision<?> clockInvNonStrictDecision =  clockInv.getDecision();
		if (clockInvNonStrictDecision instanceof RangeDecision) {
			RangeDecision decision  = (RangeDecision) clockInvNonStrictDecision;
			//CDD[] childs = clockInv.getChilds();
			// Was soll das int childs bei getOp???? offensichtlich nicht die Anzahl der Kinder?????
			// Theorie: childs = 0 -> root node. Kann aber nicht sein, bei childs = 0 immer LT o. LTEQ
			//int numChilds = childs.length;
			int OP = decision.getOp(0);
			if (OP == RangeDecision.OP_LTEQ) { // c <= T
				CDD strictClockInv = RangeDecision.create(decision.getVar(), RangeDecision.OP_LT, decision.getVal(0));
				return strictClockInv; // c < T
			}
			else if (OP == RangeDecision.OP_GTEQ) {  // c >= T
				CDD strictClockInv = RangeDecision.create(decision.getVar(), RangeDecision.OP_GT, decision.getVal(0));
				return strictClockInv; // c > T
			}
			else { // already strict 
				return clockInv;
			}
		}
		return clockInv;
		
	}
}
