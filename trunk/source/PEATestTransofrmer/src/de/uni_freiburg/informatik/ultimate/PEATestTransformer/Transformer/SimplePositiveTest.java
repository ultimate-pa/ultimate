package de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import pea.CDD;
import pea.PhaseEventAutomata;
import pea.Transition;
import srParse.pattern.PatternType;

/**
 * Transforms one of the automata (TODO: currently the first) into an automaton having the negation 
 * of the effect originally intended on the edge the effect is caused. This means that a requirement 
 * making a true MUST be the one making a true because !a must be true before.
 * This guarantees that the requirement is indeed the requirement that is responsible for the effect
 * and not just true by the preceding state.
 * TODO: get number from sysinfo
 * @author Langenfeld
 *
 */
public class SimplePositiveTest extends ClosedWorldTransformator {

	private int requirementNumber = 0;

	public SimplePositiveTest(SystemInformation sysInfo) {
		super(sysInfo);
		// TODO Auto-generated constructor stub
	}
	
	@Override
	protected PhaseEventAutomata GlobalInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s) {
		PhaseEventAutomata pea = super.GlobalInvariantPattern(pattern, p, q, r, s);
		if(this.requirementNumber == 0){
			Transition transition = pea.getPhases()[0].getTransitions().get(0);
			transition.setGuard(transition.getGuard().and(s.negate()));
		}
		return pea;
	}

	@Override
	protected PhaseEventAutomata AfterUniversality(PatternType pattern, CDD p, CDD q, CDD r, CDD s) {
		PhaseEventAutomata pea = super.AfterUniversality(pattern, p, q, r, s);
		if(this.requirementNumber == 0){
			Transition transition = pea.getPhases()[0].getTransitions().get(1);
			transition.setGuard(s.negate());
		}
		return pea;
	}
	
	

}
