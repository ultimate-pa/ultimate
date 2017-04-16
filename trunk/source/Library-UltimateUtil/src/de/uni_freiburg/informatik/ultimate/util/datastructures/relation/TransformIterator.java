/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures.relation;

import java.util.Iterator;
import java.util.function.Function;

/**
 * Takes an existing iterator and transforms each element before returning.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param IE
 *            type of input elements
 * @param OE
 *            element output elements
 */
public class TransformIterator<IE, OE> implements Iterator<OE> {

	private final Iterator<IE> mIputIterator;
	private final Function<IE, OE> mTransformer;

	public TransformIterator(final Iterator<IE> inputIterator, final Function<IE, OE> transformer) {
		mIputIterator = inputIterator;
		mTransformer = transformer;
	}

	@Override
	public boolean hasNext() {
		return mIputIterator.hasNext();
	}

	@Override
	public OE next() {
		return mTransformer.apply(mIputIterator.next());
	}

}
