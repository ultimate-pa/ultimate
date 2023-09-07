package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import java.util.Collection;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class ExtractedLocationInvariant extends ExtractedWitnessInvariant {
	private final boolean mIsBefore;

	public ExtractedLocationInvariant(final String invariant, final Collection<String> nodeLabel, final IASTNode match,
			final boolean isBefore) {
		super(invariant, nodeLabel, match);
		mIsBefore = isBefore;
	}

	public boolean isBefore() {
		return mIsBefore;
	}

	@Override
	public ExpressionResult transform(final ILocation loc, final IDispatcher dispatcher,
			final ExpressionResult expressionResult) {
		final ExpressionResult invariantExprResult = instrument(loc, dispatcher);
		if (mIsBefore) {
			return new ExpressionResultBuilder(invariantExprResult).addAllIncludingLrValue(expressionResult).build();
		}
		return new ExpressionResultBuilder(expressionResult).addAllExceptLrValue(invariantExprResult).build();
	}

	@Override
	public String getLocationDescription() {
		return "Location invariant " + (mIsBefore ? "before" : "after");
	}
}
