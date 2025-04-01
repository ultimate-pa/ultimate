package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public interface JavaCodeEdge {
	IcfgLocation getSource();

	IcfgLocation getTarget();

	boolean guard(SimpleState currentState);

	SimpleState update(SimpleState currentState);
}
