package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;

public class NestedLassoRun<LETTER,STATE> {
	private NestedRun<LETTER,STATE> stem;
	private NestedRun<LETTER,STATE> loop;
		
	public NestedLassoRun(NestedRun<LETTER,STATE> stem, NestedRun<LETTER, STATE> loop) {
		this.stem = stem;
		this.loop = loop;
	}
	
	public NestedRun<LETTER,STATE> getStem() {
		return stem;
	}
	
	public NestedRun<LETTER,STATE> getLoop() {
		return loop;
	}
	
	public NestedLassoWord<LETTER> getNestedLassoWord() {
		return new NestedLassoWord<LETTER>(this.getStem().getWord(), 
									  this.getLoop().getWord());
	}
	
	public String toString() {
		return "Stem: " + stem + " Loop:" + loop;
	}
	
	
}
