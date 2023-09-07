/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils;

import java.util.Comparator;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * Terms with greater treesize are considered smaller according to this
 * {@link Comparator}. Uses another comparator if both terms have the
 * same treesize (order has to be total).
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class TreeSizeComperator implements Comparator<Term> {

	final Comparator<Term> mTieBreaker;

	/**
	 * @param tieBreaker Additonal comparator that we use if both terms have the
	 *                   same treesize.
	 */
	public TreeSizeComperator(Comparator<Term> tieBreaker) {
		super();
		mTieBreaker = tieBreaker;
	}

	@Override
	public int compare(final Term t1, final Term t2) {
		final long size1 = new DAGSize().treesize(t1);
		final long size2 = new DAGSize().treesize(t2);
		if (size1 - size2 == 0) {
			return mTieBreaker.compare(t1, t2);
		} else {
			if (size1 - size2 > 0) {
				// first has greater size and is hence small in this order
				return -1;
			} else {
				return 1;
			}
		}
	}

}
