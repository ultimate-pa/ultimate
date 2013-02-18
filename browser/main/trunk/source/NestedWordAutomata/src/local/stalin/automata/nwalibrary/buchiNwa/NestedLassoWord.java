package local.stalin.automata.nwalibrary.buchiNwa;

import local.stalin.automata.nwalibrary.NestedWord;

public class NestedLassoWord<S> {
	private NestedWord<S> stem;
	private NestedWord<S> loop;
		
	public NestedLassoWord(NestedWord<S> stem, NestedWord<S> loop) {
		this.stem = stem;
		this.loop = loop;
	}
	
	public NestedWord<S> getStem() {
		return stem;
	}
	
	public NestedWord<S> getLoop() {
		return loop;
	}
	
	public String toString() {
		return "[  " + stem.toString() + " , " + loop.toString() + " ]";
	}
	
}
