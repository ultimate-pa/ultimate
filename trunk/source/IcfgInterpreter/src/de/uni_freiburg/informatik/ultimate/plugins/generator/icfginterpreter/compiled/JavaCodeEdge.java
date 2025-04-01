package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public interface JavaCodeEdge<T extends Enum<T> & IVariableName> {
	IcfgLocation getSource();

	IcfgLocation getTarget();

	boolean guard(EnumState<T> currentState);

	EnumState<T> update(EnumState<T> currentState);
}
