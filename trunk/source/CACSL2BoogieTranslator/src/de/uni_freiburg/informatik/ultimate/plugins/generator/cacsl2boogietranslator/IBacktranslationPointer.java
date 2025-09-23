package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public interface IBacktranslationPointer {
	List<Pair<Expression, Collection<IExpressionOrPointer>>>
			collectAllPointers(List<Pair<Expression, Collection<Expression>>> oldEntries);

	BacktranslatedACSLValue translatePointer(final IPointerValue pointer);
}
