/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.heapsplitter;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class HeapArrayReplacer extends BoogieTransformer {

	private final AddressStoreFactory mAsFac;
	private final UnionFind<AddressStore> mUf;
	private final Map<AddressStore, String> mRepToNewHeapArray;

	public HeapArrayReplacer(final AddressStoreFactory asfac, final MayAlias ma,
			final Map<AddressStore, String> repToArray) {
		mAsFac = asfac;
		mUf = ma.getAddressStores();
		mRepToNewHeapArray = repToArray;
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		if (expr instanceof ArrayAccessExpression) {
			final ArrayAccessExpression aaexpr = (ArrayAccessExpression) expr;
			final Expression arr = processExpression(aaexpr.getArray());
			final Expression[] indices = processExpressions(aaexpr.getIndices());
			final Expression[] newIndices = processExpressions(indices);
			if (arr instanceof IdentifierExpression) {
				final IdentifierExpression ie = (IdentifierExpression) arr;
				if (isHeap(ie.getIdentifier())) {
					final Expression pointerBaseExpr = newIndices[0];
					final PointerBase pointerBase = HeapSplitter.extractPointerBase(mAsFac, aaexpr);
					final AddressStore rep = mUf.find(pointerBase);
					final Expression newArray = null;
					final ArrayAccessExpression result = new ArrayAccessExpression(aaexpr.getLocation(),
							aaexpr.getType(), newArray, newIndices);
					ModelUtils.copyAnnotations(expr, result);
					return result;
				}
			}
		}
		return super.processExpression(expr);
	}

	private boolean isHeap(final String identifier) {
		return identifier.equals("#memory_int");
	}

}
