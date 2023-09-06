package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import java.util.ArrayList;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class ExtractedLoopInvariant extends ExtractedWitnessInvariant {
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
				final WhileStatement whileOld = (WhileStatement) st;
				statements.add(new WhileStatement(loc, whileOld.getCondition(), DataStructureUtils
						.concat(whileOld.getInvariants(), extractLoopInvariants(invariantExprResult, loc)),
						whileOld.getBody()));
			} else {
				statements.add(st);
			}
		}
		if (hasLoop) {
			return new ExpressionResultBuilder(expressionResult).resetStatements(statements).build();
		}
		// We might identify sth. that is not a loop (e.g. goto) as a loop.
		// We cannot annotate it with a a LoopInvariantSpecification, so we just insert an assert in that case.
		return new ExpressionResultBuilder(invariantExprResult).addAllIncludingLrValue(expressionResult).build();
	}

	private static LoopInvariantSpecification[] extractLoopInvariants(final ExpressionResult result,
			final ILocation loc) {
		final List<LoopInvariantSpecification> specs = new ArrayList<>();
		for (final Statement st : result.getStatements()) {
			if (st instanceof AssertStatement) {
				final LoopInvariantSpecification spec =
						new LoopInvariantSpecification(loc, false, ((AssertStatement) st).getFormula());
				final Check check = new Check(Check.Spec.WITNESS_INVARIANT);
				check.annotate(spec);
				specs.add(spec);
			} else {
				throw new AssertionError(st.getClass().getSimpleName() + " is not supported as annotation of a loop.");
			}
		}
		return specs.toArray(LoopInvariantSpecification[]::new);
	}

	@Override
	protected String getLocationDescription() {
		return "Loop invariant at";
	}
}
