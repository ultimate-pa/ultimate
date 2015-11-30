package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class OctagonDomain implements IAbstractDomain<OctagonDomainState, CodeBlock, IBoogieVar> {

	@Override
	public OctagonDomainState createFreshState() {
		return OctagonDomainState.createFreshState();
	}

	@Override
	public IAbstractStateBinaryOperator<OctagonDomainState> getWideningOperator() {
		return new IAbstractStateBinaryOperator<OctagonDomainState>() {
			@Override
			public OctagonDomainState apply(OctagonDomainState first, OctagonDomainState second) {
				return first.widen(second);
			}
		};
	}

	@Override
	public IAbstractStateBinaryOperator<OctagonDomainState> getMergeOperator() {
		return new IAbstractStateBinaryOperator<OctagonDomainState>() {
			@Override
			public OctagonDomainState apply(OctagonDomainState first, OctagonDomainState second) {
				return first.join(second);
			}
		};
	}

	@Override
	public IAbstractPostOperator<OctagonDomainState, CodeBlock, IBoogieVar> getPostOperator() {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	
}
