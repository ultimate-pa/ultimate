package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * The post operator of the interval domain.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 */
public class IntervalPostOperator implements IAbstractPostOperator<CodeBlock, BoogieVar> {

	private final IUltimateServiceProvider mServices;
	private final IntervalStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final RcfgStatementExtractor mStatementExtractor;
	private final IntervalDomainStatementProcessor mStatementProcessor;

	public IntervalPostOperator(IUltimateServiceProvider services,
	        IntervalStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mServices = services;
		mStateConverter = stateConverter;
		mStatementExtractor = new RcfgStatementExtractor();
		mStatementProcessor = new IntervalDomainStatementProcessor(services, mStateConverter);
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> apply(IAbstractState<CodeBlock, BoogieVar> oldstate, CodeBlock codeBlock) {
		final IntervalDomainState<CodeBlock, BoogieVar> concreteOldState = mStateConverter.getCheckedState(oldstate);

		IntervalDomainState<CodeBlock, BoogieVar> currentState = (IntervalDomainState<CodeBlock, BoogieVar>) concreteOldState
		        .copy();

		final List<Statement> statements = mStatementExtractor.process(codeBlock);
		for (final Statement stmt : statements) {
			currentState = mStatementProcessor.process(currentState, stmt);
		}
		
		return null;
	}
}
