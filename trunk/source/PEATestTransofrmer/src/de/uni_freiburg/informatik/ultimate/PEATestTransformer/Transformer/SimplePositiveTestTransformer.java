package de.uni_freiburg.informatik.ultimate.PEATestTransformer.Transformer;

import de.uni_freiburg.informatik.ultimate.PEATestTransformer.SystemInformation;
import pea.CDD;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.Transition;
import srParse.pattern.PatternType;

/**
 * Transforms one of the automata (TODO: currently the first) into an automaton
 * having the negation of the effect originally intended on the edge the effect
 * is caused. This means that a requirement making a true MUST be the one making
 * a true because !a must be true before. This guarantees that the requirement
 * is indeed the requirement that is responsible for the effect and not just
 * true by the preceding state. TODO: get number from sysinfo
 * 
 * @author Langenfeld
 *
 */
public class SimplePositiveTestTransformer extends ClosedWorldTransformator {

	private int requirementNumber = 0;

	public SimplePositiveTestTransformer(SystemInformation sysInfo) {
		super(sysInfo);
		// TODO Auto-generated constructor stub
	}

	@Override
	protected PhaseEventAutomata GlobalInvariantPattern(PatternType pattern, CDD p, CDD q, CDD r, CDD s) {
		PhaseEventAutomata pea = super.GlobalInvariantPattern(pattern, p, q, r, s);
		PhaseEventAutomata trapAutomaton = pea;
		if (this.requirementNumber == 0) {
			// bild phases
			Phase init = new Phase("stinit", p.negate());
			Phase trap = new Phase("sttrap", p.and(s));
			//init selfloop + closed world guard
			init.addTransition(init, p.prime().negate().and(this.createClosedWorldGuard(s)), new String[] {});
			//trap edge
			init.addTransition(trap, s.negate(), new String[] {});
			//create automaton
			trapAutomaton = new PhaseEventAutomata("trap_" + pea.getName(), new Phase[] { init, trap },
					new Phase[] { init }, pea.getClocks(), pea.getVariables(), pea.getEvents(), pea.getDeclarations());
			//Transition transition = pea.getPhases()[0].getTransitions().get(0);
			//transition.setGuard(transition.getGuard().and(s.negate()));
		}
		this.requirementNumber++;
		return trapAutomaton;
	}

	@Override
	protected PhaseEventAutomata AfterUniversality(PatternType pattern, CDD p, CDD q, CDD r, CDD s) {
		PhaseEventAutomata pea = super.AfterUniversality(pattern, p, q, r, s);
		if (this.requirementNumber == 0) {
			Transition transition = pea.getPhases()[0].getTransitions().get(1);
			transition.setGuard(p.negate());
		}
		this.requirementNumber++;
		return pea;
	}

}
