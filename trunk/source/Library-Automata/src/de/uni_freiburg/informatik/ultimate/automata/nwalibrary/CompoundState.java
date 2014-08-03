package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class CompoundState<STATE> {
	final Collection<STATE> states;
	
	public CompoundState(Collection<STATE> states) {
		this.states = states;
	}
	
	public String toString() {
		return states.toString();
	}
	
	public Collection<STATE> getStates() {
		return states;
	}

	@Override
	public boolean equals(Object arg0) {
		if (!(arg0 instanceof CompoundState<?>)) {
			return false;
		} 
		return ((CompoundState<?>) arg0).getStates().equals(this.getStates());
	}

	@Override
	public int hashCode() {
		int hc = 0;
		for (STATE s : states) {
			hc += HashUtils.hashJenkins(31, s);
		}
		return hc;
	}
	
	
}
