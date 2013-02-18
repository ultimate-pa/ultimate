package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;

public class NestedLassoWord<LETTER> {
	private NestedWord<LETTER> stem;
	private NestedWord<LETTER> loop;
		
	public NestedLassoWord(NestedWord<LETTER> stem, NestedWord<LETTER> loop) {
		this.stem = stem;
		this.loop = loop;
	}
	
	public NestedWord<LETTER> getStem() {
		return stem;
	}
	
	public NestedWord<LETTER> getLoop() {
		return loop;
	}
	
	public String toString() {
		return "[  " + stem.toString() + " , " + loop.toString() + " ]";
	}
	
}
