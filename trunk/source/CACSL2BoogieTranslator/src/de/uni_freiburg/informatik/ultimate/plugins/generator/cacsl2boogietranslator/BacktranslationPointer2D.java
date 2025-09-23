package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.BacktranslatedACSLValue.BacktranslatedExpression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.BacktranslatedACSLValue.FakePointer2D;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class BacktranslationPointer2D implements IBacktranslationPointer {
	private final CACSL2BoogieBacktranslator mBacktranslator;

	public BacktranslationPointer2D(final CACSL2BoogieBacktranslator backtranslator) {
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

	private Pair<Expression, Collection<IExpressionOrPointer>>
			extractTemporaryPointerExpression(final List<Pair<Expression, Collection<Expression>>> oldEntries) {
		// Find pointer base expressions in oldEntries, merge them with matching pointer offset expressions,
		// and move the combined expression to newEntries.
		// (We do a reversed by-index iteration over oldEntries so we can safely call remove() for the index.)
		for (int i = oldEntries.size() - 1; i >= 0; i--) {
			final Pair<Expression, Collection<Expression>> entry = oldEntries.get(i);

			// Check if the current entry is the base of a pointer struct
			final var pointerVariable = PointerVariable2D.fromBaseExpression(entry.getFirst());
			if (pointerVariable == null) {
				continue;
			}

			// Find a matching offset expression for the same pointer struct.
			// (We do a reversed by-index iteration over oldEntries so we can safely call remove() for the offset.)
			for (int j = oldEntries.size() - 1; j >= 0; j--) {
				final Pair<Expression, Collection<Expression>> otherentry = oldEntries.get(j);
				if (!pointerVariable.isMatchingPointerOffset(otherentry.getFirst())) {
					continue;
				}

				if (entry.getSecond().size() != 1 || otherentry.getSecond().size() != 1) {
					mBacktranslator.reportUnfinishedBacktranslation("Pointers with multiple values");
				}
				final var valueBase = DataStructureUtils.getOneAndOnly(entry.getSecond(), "pointer base");
				final var valueOffset = DataStructureUtils.getOneAndOnly(otherentry.getSecond(), "pointer offset");
				final var pointerValue = new PointerValue2D(valueBase, valueOffset);

				// Remove the now obsolete entries.
				oldEntries.remove(entry);
				oldEntries.remove(otherentry);

				// must be a mutable list, so do not use List.of(pointerValue) here
				final var values = new ArrayList<IExpressionOrPointer>();
				values.add(pointerValue);
				return new Pair<>(pointerVariable.toExpression(), values);
			}
		}
		return null;
	}

	@Override
	public BacktranslatedACSLValue translatePointer(final IPointerValue pointer) {
		assert pointer instanceof PointerValue2D : "pointer must be a PointerValue2D";
		final PointerValue2D ptr2D = (PointerValue2D) pointer;

		final BacktranslatedExpression base = mBacktranslator.translateExpression(ptr2D.base());
		if (!base.range().isSingleton()) {
			mBacktranslator.reportUnfinishedBacktranslation("Pointer with non-unique base value");
			return null;
		}
		final BigInteger baseValue = base.range().getMinValue();

		final BacktranslatedExpression offset = mBacktranslator.translateExpression(ptr2D.offset());
		if (!offset.range().isSingleton()) {
			mBacktranslator.reportUnfinishedBacktranslation("Pointer with non-unique base value");
			return null;
		}
		final BigInteger offsetValue = offset.range().getMinValue();

		// Create a value like {base:offset}
		// This is not a real ACSL expression, so we wrap it into FakePointer.
		return new FakePointer2D(baseValue, offsetValue);
	}
}
