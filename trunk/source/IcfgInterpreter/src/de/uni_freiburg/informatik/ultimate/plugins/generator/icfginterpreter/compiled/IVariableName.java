package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.compiled;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;

public interface IVariableName {
	void initiate(final HashSet<IProgramVar> progVars);

	IProgramVar getProgramVar();
}