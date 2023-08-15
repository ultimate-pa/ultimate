package de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

public class PeaPhaseProgramCounter {

	private final int pc;
	private final Phase phase;
	private final PhaseEventAutomata pea;
	private final PatternType<?> req;
	
	public PeaPhaseProgramCounter(int pc, Phase phase, PhaseEventAutomata pea, PatternType<?> req) {
		super();
		this.pc = pc;
		this.phase = phase;
		this.pea = pea;
		this.req = req;
	}

	@Override
	public int hashCode() {
		return phase.getName().hashCode();
	}
	
	@Override
	public boolean equals(Object o) {
		if(this == o) {
			return true;
		}
		if(o instanceof Phase) {
			Phase oPhase = (Phase) o;
			return phase.getName().equals(oPhase.getName());
		}
		return false;
	}

	public int getPc() {
		return pc;
	}

	public Phase getPhase() {
		return phase;
	}

	public PhaseEventAutomata getPea() {
		return pea;
	}
	
	public PatternType<?> getReq() {
		return req;
	}
}
