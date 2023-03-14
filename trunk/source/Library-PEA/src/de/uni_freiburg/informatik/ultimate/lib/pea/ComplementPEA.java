package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.ArrayList;
import java.util.List;



/**
 * This class implements an algorithm for complementing Phase Event Automata as described in my bachelors thesis.
 * Documentation to be continued...
 *
 * TODO: split Alg up in multiple methods
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
		
		computeInitialTransitionSink(sinkPhase);
		
		for (Phase phase : mPEAtoComplement.getPhases()) {
			CDD clockInv = phase.getClockInvariant();
			Decision<?> clockDecision = clockInv.getDecision();
			CDD guardToSink = phase.stateInv.and(RangeDecision.strict(clockInv));
			// create new phase for complement automaton that is not accepting
			Phase newPhase = new Phase(phase.name, phase.stateInv, phase.clockInv);
			newPhase.setTerminal(false);
			
			
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
			
			Decision<?> newClockDecision = newPhase.getClockInvariant().getDecision();
			
			// special case: clock invariant is  c < T
			if (clockDecision instanceof RangeDecision) {
				// make clock invariant non-strict
				RangeDecision newClockInv = (RangeDecision) newClockDecision;
				// because all clock invariants are convex, we know that the true Child is always 0.
				if (newClockInv.getOp(0) == RangeDecision.OP_LT) {
					newPhase.clockInv = RangeDecision.create(newClockInv.getVar(), RangeDecision.OP_LTEQ, newClockInv.getVal(0));
				}
				for (Transition transition : newPhase.transitions) {
					CDD newGuard = transition.getGuard().and(RangeDecision.create(newClockInv.getVar(), RangeDecision.OP_LT, newClockInv.getVal(0)));
					transition.setGuard(newGuard);
				}
			}
		}
		PhaseEventAutomata complementedPEA = new PhaseEventAutomata(mPEAtoComplement.getName() + "_c",  phases.toArray(new Phase[0]), mPEAtoComplement.mInit);
		return complementedPEA;
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
			sinkPhase.setInit(true);
			InitialTransition sinkInitialTransition = new InitialTransition(initialTransitionSinkGuard.negate(), sinkPhase);
			sinkPhase.setInitialTransition(sinkInitialTransition);
		} else {
			sinkPhase.setInit(false);
		}
	}
}
