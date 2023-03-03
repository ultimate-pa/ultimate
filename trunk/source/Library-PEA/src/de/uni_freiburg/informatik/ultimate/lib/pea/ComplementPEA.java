package de.uni_freiburg.informatik.ultimate.lib.pea;

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
			CDD guardToSink = phase.stateInv.and(strict(phase.clockInv, CDD.TRUE));
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
					CDD noResetClockInv = noReset(successorClockInv, reset, noResetCdd);
					guardToSink = guardToSink.or(transition.getGuard().and(successorStateInv).and(strict(noResetClockInv, strictCdd)));
				} else {
					guardToSink = guardToSink.or(transition.getGuard().and(successorStateInv).and(strict(successorClockInv, strictCdd)));
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
	
	/**
	 * Computes a CDD representing strict(clockInv
	 * TODO: move to RangeDecision Class
	 * 
	 * @param clockInv: the clock invariant that will be strictified
	 */
	public CDD strict(CDD clockInv, CDD strict) {
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
				strict = strict.and(strictClockInv); // c < T
			}
			// Dieser Fall würde nie eintreten??? 
			// ähnliches Problem bei val(int childs)
			else if (OP == RangeDecision.OP_GTEQ) {  // c >= T
				CDD strictClockInv = RangeDecision.create(decision.getVar(), RangeDecision.OP_GT, decision.getVal(0));
				strict.and(strictClockInv); // c > T
			}
			else { // already strict 
				strict.and(clockInv);
			}
			for (CDD child : clockInv.getChilds()) {
				return strict(child, strict);
			}
		}
		return strict;
	}
	
	
	/**
	 * Computes a CDD representing the conjunction of the RangeDecision-Nodes in the CDD given 
	 * that are NOT in the reset set also given.
	 * 
	 * TODO move to RangeDecision class
	 * TODO rename filterCDDbyArray()
	 * 
	 * @param clockInv: Clock invariant of some phase.
	 * 
	 * @param reset: the reset set of an incoming transition of that phase.
	 */
	public CDD noReset(CDD clockInv, String[] reset, CDD noReset) {
		if (clockInv.getChilds() == null) { // terminal node
			return noReset; // no clock invariant
		}
		Decision<?> clockInvDecision = clockInv.getDecision();
		if (clockInvDecision instanceof RangeDecision) {
			RangeDecision decision = (RangeDecision) clockInvDecision;
			// if the variable of the decision is not in reset, we compute the conjunction
			if (!Arrays.asList(reset).contains(decision.getVar())) {
				CDD newDecision = RangeDecision.create(decision.getVar(), decision.getOp(0), decision.getVal(0));
				noReset = noReset.and(newDecision);
			}
			CDD[] childs = clockInv.getChilds();
			for (CDD cdd : childs) {
				return noReset(cdd, reset, noReset);
			}
		}
		return noReset;
	}
	
}
