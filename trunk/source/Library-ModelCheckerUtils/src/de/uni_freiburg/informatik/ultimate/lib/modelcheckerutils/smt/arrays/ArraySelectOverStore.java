/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**

 * @author Matthias Heizmann
 */
public class ArraySelectOverStore {
	private final ArrayStore mArrayStore;
	private final Term mIndex;

	public ArraySelectOverStore(final Term term) {
		try {
			final ArraySelect arraySelect = ArraySelect.convert(term);
			mArrayStore = ArrayStore.convert(arraySelect.getArray());
			mIndex = arraySelect.getIndex();
		} catch (final IllegalArgumentException iae) {
			throw iae;
		}
	}

	public ArrayStore getArrayStore() {
		return mArrayStore;
	}

	public Term getIndex() {
		return mIndex;
	}

	public Term toTerm(final Script script) {
		return script.term("select", getArrayStore().asTerm(), getIndex());
	}


	@Override
	public String toString() {
		return String.format("(select %s %s)", getArrayStore(), getIndex());
	}



	public static ArraySelectOverStore convert(final Term term) {
		try {
			return new ArraySelectOverStore(term);
		} catch (final IllegalArgumentException iae) {
			return null;
		}
	}
}
