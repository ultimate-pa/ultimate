package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IEqualityProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;

/**
 * Default equality provider for domains that deal with Boogie statements, variables, code blocks, and expressions.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            The type of the abstract states handled by the equality provider.
 */
public class DefaultEqualityProvider<STATE extends IAbstractState<STATE, CodeBlock, IBoogieVar>>
        implements IEqualityProvider<STATE, CodeBlock, IBoogieVar, Expression> {

	private final IAbstractPostOperator<STATE, CodeBlock, IBoogieVar> mPostOperator;
	private final CodeBlockFactory mCodeBlockFactory;

	public DefaultEqualityProvider(final IAbstractPostOperator<STATE, CodeBlock, IBoogieVar> postOperator,
	        final RootAnnot rootAnnotation) {
		mPostOperator = postOperator;
		mCodeBlockFactory = rootAnnotation.getCodeBlockFactory();
	}

	@Override
	public boolean isDefinitelyEqual(STATE state, Expression first, Expression second) {
		return checkVariableParameters(state, first, second, Operator.COMPNEQ);
	}
	
	@Override
	public boolean isDefinitelyNotEqual(STATE state, Expression first, Expression second) {
		return checkVariableParameters(state, first, second, Operator.COMPEQ);
	}

	private boolean checkVariableParameters(STATE state, Expression first, Expression second, final Operator operator) {
		assert state != null;
		assert first != null;
		assert second != null;

		final Expression formula = new BinaryExpression(null, operator, first, second);
		final AssumeStatement assumeStatement = new AssumeStatement(null, formula);

		final CodeBlock assumeCodeBlock = mCodeBlockFactory.constructStatementSequence(null, null,
		        Stream.of(assumeStatement).collect(Collectors.toList()), Origin.IMPLEMENTATION);

		final List<STATE> postReturn = mPostOperator.apply(state, assumeCodeBlock);
		assert postReturn.size() == 1;

		return postReturn.get(0).isBottom();
	}

}
