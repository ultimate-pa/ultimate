package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class ArrayGroup {
	private final Set<IProgramVarOrConst> mArraysInThisGroup;

	public ArrayGroup(final Set<IProgramVarOrConst> block) {
		mArraysInThisGroup = Collections.unmodifiableSet(block);
	}

	Set<IProgramVarOrConst> getArrays() {
		return mArraysInThisGroup;
	}
}
