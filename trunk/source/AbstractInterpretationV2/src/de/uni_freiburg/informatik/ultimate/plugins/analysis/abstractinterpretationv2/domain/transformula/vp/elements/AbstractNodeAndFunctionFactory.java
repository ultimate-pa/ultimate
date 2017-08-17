package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.AbstractCCElementFactory;

public abstract class AbstractNodeAndFunctionFactory<
		NODE extends IEqNodeIdentifier<NODE, FUNCTION>,
		FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>,
		CONTENT>
			extends AbstractCCElementFactory<NODE, FUNCTION, CONTENT> {


	public abstract NODE getOrConstructNode(CONTENT c);

	public abstract FUNCTION getOrConstructFunction(Term term);

	public abstract FUNCTION getExistingFunction(Term term);

	public abstract NODE getExistingNode(Term term);
}
