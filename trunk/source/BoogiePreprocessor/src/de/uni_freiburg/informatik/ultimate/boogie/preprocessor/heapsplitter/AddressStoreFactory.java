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

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class AddressStoreFactory {
	private final Map<BigInteger, PointerBaseIntLiteral> mInt = new HashMap<>();
	private final NestedMap2<String, DeclarationInformation, PointerBaseVariable> mVariable = new NestedMap2<>();
	private final Map<PointerBase, MemorySegment> mSegment = new HashMap<>();

	public PointerBaseIntLiteral getPointerBase(final BigInteger bi) {
		return mInt.computeIfAbsent(bi, x -> new PointerBaseIntLiteral(x));
	}

	public PointerBaseVariable getPointerBase(final String id, final DeclarationInformation delcInfo) {
		final Function<String, Function<? super DeclarationInformation, ? extends PointerBaseVariable>> func = (x -> (y -> new PointerBaseVariable(
				x)));
		return mVariable.computeIfAbsent(id, delcInfo, func);
	}

	public MemorySegment getMemorySegment(final PointerBase pointerBase) {
		return mSegment.computeIfAbsent(pointerBase, x -> new MemorySegment(pointerBase));
	}

}