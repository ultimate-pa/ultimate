package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * This abstract domain keeps track of the sign of each variable during abstract interpretation. Variables can either be
 * negative, equal to 0, or positive.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 * @param <CodeBlock>
 *            Any action type.
 * @param <BoogieVar>
 *            Any variable declaration.
 */
public class SignDomain implements IAbstractDomain<SignDomainState<CodeBlock, BoogieVar>, CodeBlock, BoogieVar> {

	private SignStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final IUltimateServiceProvider mServices;

	public SignDomain(IUltimateServiceProvider services) {
		mServices = services;
		mStateConverter = new SignStateConverter<CodeBlock, BoogieVar>(new SignDomainState<CodeBlock, BoogieVar>());
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> createFreshState() {
		return new SignDomainState<CodeBlock, BoogieVar>();
	}

	@Override
	public IAbstractStateBinaryOperator<CodeBlock, BoogieVar> getWideningOperator() {
		return new SignMergeOperator<CodeBlock, BoogieVar>(mStateConverter);
	}

	@Override
	public IAbstractStateBinaryOperator<CodeBlock, BoogieVar> getMergeOperator() {
		return new SignMergeOperator<CodeBlock, BoogieVar>(mStateConverter);
	}

	@Override
	public IAbstractPostOperator<CodeBlock, BoogieVar> getPostOperator() {
		return new SignPostOperator(mServices, mStateConverter);
	}

	@Override
	public Class<SignDomainState<CodeBlock, BoogieVar>> getAbstractStateClass() {
		return mStateConverter.getAbstractStateClass();
	}

}
