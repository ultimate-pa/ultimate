/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers;

import java.util.List;

/**
 * Remembers and re-identifies (usually failed) variants, optionally in a memory efficient manner.
 * It can be used to prevent duplicate tests with certain minimizers (especially ddmin). The idea is that the actual
 * lists are not as in a real Set, because a retrieval of the stored lists is not required. This interface allows
 * implementations to be switched for a different memory footprint/lookup overhead ratio.
 *
 * @param <E>
 *            element type
 */
public interface IDuplicateVariantTracker<E> {
	
	/**
	 * Remember the given variant subsequence.
	 *
	 * @param variant
	 *            variant
	 */
	void add(List<? extends E> variant);
	
	/**
	 * Returns whether the given variant has been add before. False negative results are explicitly allowed (resulting
	 * in duplicate tests), but false positives should be avoided, because that would cause certain variants to be never
	 * tested.
	 *
	 * @param variant
	 *            variant
	 * @return true if the variant has been added before (and not removed by a call to removeLargerVariants)
	 */
	boolean contains(List<? extends E> variant);
	
	/**
	 * Remove all stored variants that are not smaller than keptVariantSize.
	 * Optional method to reduce memory footprint even more by removing all larger variants each time a valid variant
	 * has been found, because once that happens all subsequent variants should be subsequences of that.
	 *
	 * @param keptVariantSize
	 *            variant size bound
	 */
	void removeLargerVariants(int keptVariantSize);
}
