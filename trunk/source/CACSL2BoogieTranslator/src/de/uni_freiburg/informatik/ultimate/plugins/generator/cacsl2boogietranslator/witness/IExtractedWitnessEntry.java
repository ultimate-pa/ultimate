package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public interface IExtractedWitnessEntry {
	ImmutableSet<String> getNodeLabels();

	ExpressionResult transform(final ILocation loc, final IDispatcher dispatcher,
			final ExpressionResult expressionResult);
}
