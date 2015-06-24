package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Applies an ACTION to an abstract state of the {@link SignDomain}.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 * @param <ACTION>
 *            Any action type.
 * @param <VARDECL>
 *            Any variable declaration type.
 */
public class SignPostOperator implements IAbstractPostOperator<CodeBlock, BoogieVar> {

	private SignStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private RcfgStatementExtractor mStatementExtractor;
	private SignDomainStatementProcessor<CodeBlock, BoogieVar> mStatementProcessor;

	protected SignPostOperator(SignStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mStateConverter = stateConverter;
		mStatementExtractor = new RcfgStatementExtractor();
		mStatementProcessor = new SignDomainStatementProcessor<CodeBlock, BoogieVar>();
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> apply(IAbstractState<CodeBlock, BoogieVar> oldstate, CodeBlock concrete) {
		final SignDomainState<CodeBlock, BoogieVar> concreteOldState = mStateConverter.getCheckedState(oldstate);
		SignDomainState<CodeBlock, BoogieVar> interimState = concreteOldState;
		List<Statement> statements = mStatementExtractor.process(concrete);
		for (Statement stmt : statements) {
			final SignDomainState<CodeBlock, BoogieVar> currentState = mStatementProcessor.process(interimState, stmt);

//			if (interimState != null) {
//				SignMergeOperator.computeMergedValue(interimState, currentState);
//			}
		}

		return interimState;
	}
}
