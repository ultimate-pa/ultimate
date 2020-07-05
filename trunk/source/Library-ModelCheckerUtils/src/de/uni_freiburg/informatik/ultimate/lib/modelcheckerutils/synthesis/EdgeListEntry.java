package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.synthesis;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class EdgeListEntry {
	public IcfgLocation source;
	public IcfgLocation target;
	public Term term;
	public EdgeListEntry(IcfgLocation s, IcfgLocation t, Term te){
		source = s;
		target = t;
		term = te;
		
	}
}
