/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023-2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2025 Jan Körner
 * Copyright (C) 2025 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.BacktranslatedACSLValue.BacktranslatedExpression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.BacktranslatedACSLValue.FakePointer2D;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator.IBacktranslationPointer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator.IExpressionOrPointer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator.IPointerValue;
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

		final BacktranslatedExpression offset = mBacktranslator.translateExpression(ptr2D.offset());
		if (!offset.range().isSingleton()) {
			mBacktranslator.reportUnfinishedBacktranslation("Pointer with non-unique base value");
			return null;
		}

		// Create a value like {base:offset}
		// This is not a real ACSL expression, so we wrap it into FakePointer.
		return new FakePointer2D(base.range().getMinValue(), offset.range().getMinValue());
	}

	/**
	 * Represents a pair of values forming a pointer struct in Boogie.
	 */
	private record PointerValue2D(Expression base, Expression offset) implements IPointerValue {
		// empty
	}

	/**
	 * Represents a 2-dimensional pointer variable in Boogie.
	 *
	 * This class is only used to represent variables (keys in the program state). For values of pointer structs, use
	 * {@link PointerValue2D} instead.
	 */
	private record PointerVariable2D(ILocation loc, IdentifierExpression rawPointer, boolean isOld) {
		/**
		 * Checks if the given expression is the base of a pointer struct and returns the corresponding
		 * {@link PointerVariable2D} if so. Otherwise, returns {@code null}.
		 */
		static PointerVariable2D fromBaseExpression(final Expression expr) {
			if (expr instanceof final IdentifierExpression id && id.getIdentifier().endsWith(SFO.POINTER_BASE)) {
				final String baseName = id.getIdentifier();
				final String pointerName = baseName.substring(0, baseName.length() - SFO.POINTER_BASE.length() - 1);
				final var pointer = new IdentifierExpression(id.getLoc(), id.getType(), pointerName,
						id.getDeclarationInformation());
				return new PointerVariable2D(pointer.getLoc(), pointer, false);
			}
			if (expr instanceof final UnaryExpression unary && unary.getOperator() == Operator.OLD) {
				final var underlying = fromBaseExpression(unary.getExpr());
				if (underlying != null) {
					return new PointerVariable2D(unary.getLoc(), underlying.rawPointer(), true);
				}
			}
			return null;
		}

		/**
		 * Checks if the given expression is a variable representing an offset for this pointer variable.
		 */
		boolean isMatchingPointerOffset(final Expression expr) {
			if (isOld() && expr instanceof final UnaryExpression uExpr) {
				return uExpr.getOperator() == Operator.OLD && asNonOld().isMatchingPointerOffset(uExpr.getExpr());
			}
			if (!isOld() && expr instanceof final IdentifierExpression idExpr) {
				final var identifier = idExpr.getIdentifier();
				return identifier.startsWith(rawPointer().getIdentifier()) && identifier.endsWith(SFO.POINTER_OFFSET);
			}
			return false;
		}

		Expression toExpression() {
			if (isOld) {
				return new UnaryExpression(loc, Operator.OLD, rawPointer);
			}
			return rawPointer;
		}

		PointerVariable2D asNonOld() {
			return new PointerVariable2D(rawPointer.getLoc(), rawPointer, false);
		}
	}
}
