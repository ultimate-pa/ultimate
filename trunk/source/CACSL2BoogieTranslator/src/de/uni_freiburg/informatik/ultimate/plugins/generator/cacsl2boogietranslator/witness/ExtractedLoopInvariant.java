/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Class for a loop invariant extracted from the witness
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ExtractedLoopInvariant extends ExtractedWitnessInvariant {
	private static final boolean PRODUCE_LOOP_INVARIANTS = false;

	public ExtractedLoopInvariant(final String invariant, final Collection<String> nodeLabel, final IASTNode match) {
		super(invariant, nodeLabel, match);
	}

	@Override
	public ExpressionResult transform(final ILocation loc, final IDispatcher dispatcher,
			final ExpressionResult expressionResult) {
		final ExpressionResult invariantExprResult = instrument(loc, dispatcher);
		final List<Statement> statements = new ArrayList<>();
		boolean hasLoop = false;
		for (final Statement st : expressionResult.getStatements()) {
			if (st instanceof WhileStatement) {
				if (hasLoop) {
					throw new UnsupportedOperationException(
							"The result contains multiple loops, unable to match the invariant.");
				}
				hasLoop = true;
				final WhileStatement loop = (WhileStatement) st;
				if (PRODUCE_LOOP_INVARIANTS) {
					statements.addAll(transformLoop(invariantExprResult, loop, loc));
				} else {
					final List<Statement> witnessStatements = new ArrayList<>(invariantExprResult.getStatements());
					final Statement[] newBody =
							DataStructureUtils.concat(loop.getBody(), witnessStatements.toArray(Statement[]::new));
					statements.addAll(witnessStatements);
					statements.add(new WhileStatement(loc, loop.getCondition(), loop.getInvariants(), newBody));
				}
			} else {
				statements.add(st);
			}
		}
		if (hasLoop) {
			return new ExpressionResultBuilder(expressionResult).addAllExceptLrValueAndStatements(invariantExprResult)
					.resetStatements(statements).build();
		}
		// We might identify sth. that is not a loop (e.g. goto) as a loop.
		// We cannot annotate it with a a LoopInvariantSpecification, so we just insert an assert in that case.
		return new ExpressionResultBuilder(invariantExprResult).addAllIncludingLrValue(expressionResult).build();
	}

	private static List<Statement> transformLoop(final ExpressionResult witnessResult, final WhileStatement loop,
			final ILocation loc) {
		final List<Statement> result = new ArrayList<>();
		final List<Statement> afterLoop = new ArrayList<>();
		final List<LoopInvariantSpecification> newInvariants = new ArrayList<>(Arrays.asList(loop.getInvariants()));
		boolean loopInvariantAdded = false;
		for (final Statement st : witnessResult.getStatements()) {
			if (st instanceof AssertStatement) {
				final LoopInvariantSpecification spec =
						new LoopInvariantSpecification(loc, false, ((AssertStatement) st).getFormula());
				final Check check = new Check(Spec.WITNESS_INVARIANT);
				check.annotate(spec);
				newInvariants.add(spec);
				loopInvariantAdded = true;
			} else if (loopInvariantAdded) {
				// TODO: Check if this is only a havoc?
				afterLoop.add(st);
			} else {
				result.add(st);
			}
		}
		final Statement[] newBody = DataStructureUtils.concat(loop.getBody(), result.toArray(Statement[]::new));
		result.add(new WhileStatement(loc, loop.getCondition(),
				newInvariants.toArray(LoopInvariantSpecification[]::new), newBody));
		result.addAll(afterLoop);
		return result;
	}

	@Override
	protected String getLocationDescription() {
		return "Loop invariant at";
	}
}
