package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Set;

public class MultiElementWrapper implements IElementWrapper {
	Set<ISingleElementWrapper> mElementWrappers;

	@Override
	public Set<ISingleElementWrapper> getElements() {
		return mElementWrappers;
	}

}
