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

import java.math.BigInteger;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.BacktranslatedACSLValue.FakePointer1D;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator.IBacktranslationPointer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator.IExpressionOrPointer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator.IPointerValue;
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

	/**
	 * Represents a single value forming a pointer struct in Boogie.
	 */
	private record PointerValue1D(Expression base) implements IPointerValue {
		// empty
	}

	/**
	 * Represents a 1-dimensional pointer variable in Boogie.
	 *
	 * This class is only used to represent variables (keys in the program state). For values of pointer structs, use
	 * {@link PointerValue1D} instead.
	 */
	private record PointerVariable1D(ILocation loc, IdentifierExpression rawPointer, boolean isOld) {
		/**
		 * Checks if the given expression is the base of a pointer struct and returns the corresponding
		 * {@link PointerVariable1D} if so. Otherwise, returns {@code null}.
		 */
		static PointerVariable1D fromBaseExpression(final Expression expr) {
			if (expr instanceof final IdentifierExpression id && id.getIdentifier().endsWith(SFO.POINTER_BASE)) {
				final String baseName = id.getIdentifier();
				final String pointerName = baseName.substring(0, baseName.length() - SFO.POINTER_BASE.length() - 1);
				final var pointer = new IdentifierExpression(id.getLoc(), id.getType(), pointerName,
						id.getDeclarationInformation());
				return new PointerVariable1D(pointer.getLoc(), pointer, false);
			}
			if (expr instanceof final UnaryExpression unary && unary.getOperator() == Operator.OLD) {
				final var underlying = fromBaseExpression(unary.getExpr());
				if (underlying != null) {
					return new PointerVariable1D(unary.getLoc(), underlying.rawPointer(), true);
				}
			}
			return null;
		}

		Expression toExpression() {
			if (isOld) {
				return new UnaryExpression(loc, Operator.OLD, rawPointer);
			}
			return rawPointer;
		}
	}
}
