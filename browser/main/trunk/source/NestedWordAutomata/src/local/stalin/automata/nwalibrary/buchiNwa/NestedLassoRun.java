package local.stalin.automata.nwalibrary.buchiNwa;

import local.stalin.automata.nwalibrary.NestedRun;

public class NestedLassoRun<S,C> {
	private NestedRun<S,C> stem;
	private NestedRun<S,C> loop;
		
	public NestedLassoRun(NestedRun<S, C> stem, NestedRun<S, C> loop) {
		this.stem = stem;
		this.loop = loop;
	}
	
	public NestedRun<S, C> getStem() {
		return stem;
	}
	
	public NestedRun<S, C> getLoop() {
		return loop;
	}
	
	public String toString() {
		return "Stem: " + stem + " Loop:" + loop;
	}
	
	
}
