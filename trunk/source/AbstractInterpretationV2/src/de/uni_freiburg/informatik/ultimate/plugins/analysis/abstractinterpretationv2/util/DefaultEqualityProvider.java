/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IEqualityProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;

/**
 * Default equality provider for domains that deal with Boogie statements, variables, code blocks, and expressions.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 *            The type of the abstract states handled by the equality provider.
 */
public class DefaultEqualityProvider<STATE extends IAbstractState<STATE>>
		implements IEqualityProvider<STATE, Expression> {

	private final IAbstractPostOperator<STATE, CodeBlock> mPostOperator;
	private final CodeBlockFactory mCodeBlockFactory;

	/**
	 * Creates an instance of a default Equality Provider for Boogie-based abstract domains.
	 *
	 * @param postOperator
	 *            The post operator of the abstract domain.
	 * @param rootAnnotation
	 *            The root annotation of the program.
	 */
	public DefaultEqualityProvider(final IAbstractPostOperator<STATE, CodeBlock> postOperator,
			final BoogieIcfgContainer rootAnnotation) {
		mPostOperator = postOperator;
		mCodeBlockFactory = rootAnnotation.getCodeBlockFactory();
	}

	@Override
	public boolean isDefinitelyEqual(final STATE state, final Expression first, final Expression second) {
		return checkVariableParameters(state, first, second, Operator.COMPNEQ);
	}

	@Override
	public boolean isDefinitelyNotEqual(final STATE state, final Expression first, final Expression second) {
		return checkVariableParameters(state, first, second, Operator.COMPEQ);
	}

	private boolean checkVariableParameters(final STATE state, final Expression first, final Expression second,
			final Operator operator) {
		assert state != null;
		assert first != null;
		assert second != null;

		final Expression formula = new BinaryExpression(null, operator, first, second);
		final AssumeStatement assumeStatement = new AssumeStatement(null, formula);

		final CodeBlock assumeCodeBlock = mCodeBlockFactory.constructStatementSequence(null, null,
				new ArrayList<>(Arrays.asList(assumeStatement)), Origin.IMPLEMENTATION);

		final Collection<STATE> postReturn = mPostOperator.apply(state, assumeCodeBlock);
		assert postReturn.size() == 1;

		return postReturn.iterator().next().isBottom();
	}

}
