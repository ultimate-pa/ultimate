package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class ArrayGroup {
	Set<IProgramVarOrConst> mArraysInThisGroup;

	Set<IProgramVarOrConst> getArrays() {
		return mArraysInThisGroup;
	}
}
