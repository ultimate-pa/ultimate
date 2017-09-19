package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.AbstractCCElementFactory;

public abstract class AbstractNodeAndFunctionFactory<NODE extends IEqNodeIdentifier<NODE>, CONTENT>
			extends AbstractCCElementFactory<NODE, CONTENT> {

	public abstract NODE getOrConstructNode(CONTENT c);

	public abstract NODE getExistingNode(CONTENT term);
}

