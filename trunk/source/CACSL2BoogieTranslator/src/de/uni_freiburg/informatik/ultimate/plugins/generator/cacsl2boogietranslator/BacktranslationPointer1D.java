package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.BacktranslatedACSLValue.BacktranslatedExpression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.BacktranslatedACSLValue.FakePointer1D;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class BacktranslationPointer1D implements IBacktranslationPointer {
	private final CACSL2BoogieBacktranslator mBacktranslator;

	public BacktranslationPointer1D(final CACSL2BoogieBacktranslator backtranslator) {
		mBacktranslator = backtranslator;
	}

	@Override
	public List<Pair<Expression, Collection<IExpressionOrPointer>>>
			collectAllPointers(final List<Pair<Expression, Collection<Expression>>> oldEntries) {

		final List<Pair<Expression, Collection<IExpressionOrPointer>>> newEntries = new ArrayList<>();

		var extractedPointer = extractTemporaryPointerExpression(oldEntries);
		while (extractedPointer != null) {
			newEntries.add(extractedPointer);
			extractedPointer = extractTemporaryPointerExpression(oldEntries);
		}

		return newEntries;
	}

	private static Pair<Expression, Collection<IExpressionOrPointer>>
			extractTemporaryPointerExpression(final List<Pair<Expression, Collection<Expression>>> oldEntries) {
		// Find pointer base expressions in oldEntries, merge them with matching pointer offset expressions,
		// and move the combined expression to newEntries.
		// (We do a reversed by-index iteration over oldEntries so we can safely call remove() for the index.)
		for (int i = oldEntries.size() - 1; i >= 0; i--) {
			final Pair<Expression, Collection<Expression>> entry = oldEntries.get(i);

			// Check if the current entry is the base of a pointer struct
			final var pointerVariable = PointerVariable1D.fromBaseExpression(entry.getFirst());
			if (pointerVariable == null) {
				continue;
			}

			final var valueBase = DataStructureUtils.getOneAndOnly(entry.getSecond(), "pointer base");
			final var pointerValue = new PointerValue1D(valueBase);

			// Remove the now obsolete entries.
			oldEntries.remove(entry);

			// must be a mutable list, so do not use List.of(pointerValue) here
			final var values = new ArrayList<IExpressionOrPointer>();
			values.add(pointerValue);
			return new Pair<>(pointerVariable.toExpression(), values);
		}
		return null;
	}

	@Override
	public BacktranslatedACSLValue translatePointer(final IPointerValue pointer) {
		assert pointer instanceof PointerValue1D : "pointer must be a PointerValue1D";
		final PointerValue1D ptr1D = (PointerValue1D) pointer;

		final BacktranslatedExpression base = mBacktranslator.translateExpression(ptr1D.base());
		if (!base.range().isSingleton()) {
			mBacktranslator.reportUnfinishedBacktranslation("Pointer with non-unique base value");
			return null;
		}
		final BigInteger baseValue = base.range().getMinValue();

		// Create a value like {base}
		// This is not a real ACSL expression, so we wrap it into FakePointer.
		return new FakePointer1D(baseValue);
	}

}
