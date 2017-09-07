package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;

public class LiteralManager<NODE extends IEqNodeIdentifier<NODE, FUNCTION>,
			FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {

	public boolean isLiteral(final NODE elem) {
		return elem.isLiteral();
	}

//	public HashRelation<NODE, NODE> getDisequalities(NODE elem, Collection<NODE> allLiteralElements) {
	public Collection<NODE> getDisequalities(final NODE elem, final Collection<NODE> allLiteralElements) {
		return allLiteralElements.stream()
				.filter(el -> el.getTerm().getSort().equals(elem.getTerm().getSort()))
				.collect(Collectors.toSet());
	}

}
