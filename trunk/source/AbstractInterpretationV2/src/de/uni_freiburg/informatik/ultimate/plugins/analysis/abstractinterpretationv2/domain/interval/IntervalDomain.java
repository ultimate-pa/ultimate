package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.math.BigDecimal;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * This abstract domain stores intervals for all variable valuations. Intervals can be of the form [num; num], where num
 * is of type {@link BigDecimal}, or of type -&infin; or &infin;, respectively. An interval may also be "{}" which
 * corresponds to the abstract state of &bot;.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalDomain implements IAbstractDomain<IntervalDomainState<CodeBlock, BoogieVar>, CodeBlock, BoogieVar> {

	private IntervalStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final IUltimateServiceProvider mServices;

	public IntervalDomain(IUltimateServiceProvider services) {
		mServices = services;
		mStateConverter = new IntervalStateConverter<CodeBlock, BoogieVar>(
		        new IntervalDomainState<CodeBlock, BoogieVar>());
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> createFreshState() {
		return new IntervalDomainState<CodeBlock, BoogieVar>(mStateConverter);
	}

	@Override
	public IAbstractStateBinaryOperator<CodeBlock, BoogieVar> getWideningOperator() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IAbstractStateBinaryOperator<CodeBlock, BoogieVar> getMergeOperator() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IAbstractPostOperator<CodeBlock, BoogieVar> getPostOperator() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Class<IntervalDomainState<CodeBlock, BoogieVar>> getAbstractStateClass() {
		// TODO Auto-generated method stub
		return null;
	}

}
