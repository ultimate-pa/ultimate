package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link IntervalDomainState} for the given statement.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalDomainStatementProcessor extends BoogieVisitor {

	private final IntervalStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final IUltimateServiceProvider mServices;

	private IntervalDomainState<CodeBlock, BoogieVar> mOldState;
	private IntervalDomainState<CodeBlock, BoogieVar> mNewState;

	protected IntervalDomainStatementProcessor(IUltimateServiceProvider services,
	        IntervalStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mStateConverter = stateConverter;
		mServices = services;
	}

	public IntervalDomainState<CodeBlock, BoogieVar> process(IntervalDomainState<CodeBlock, BoogieVar> oldState,
	        Statement statement) {

		assert oldState != null;
		assert statement != null;

		mOldState = oldState;
		mNewState = (IntervalDomainState<CodeBlock, BoogieVar>) mOldState.copy();
		
		processStatement(statement);
		
		return mNewState;
	}
}
