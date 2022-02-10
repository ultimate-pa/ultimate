/*
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtilsTest Library.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.util.datastructures.poset;

import java.util.Set;

public class UpsideDownLattice<T> implements ILattice<Set<T>> {
	PowersetLattice<T> mPwsLattice;

	public UpsideDownLattice(final PowersetLattice<T> pwsLattice) {
		mPwsLattice = pwsLattice;
	}

	@Override
	public Set<T> getBottom() {
		// TODO Auto-generated method stub
		return mPwsLattice.getTop();
	}

	@Override
	public Set<T> getTop() {
		// TODO Auto-generated method stub
		return mPwsLattice.getBottom();
	}

	@Override
	public ComparisonResult compare(final Set<T> o1, final Set<T> o2) {
		// TODO Auto-generated method stub
		return mPwsLattice.compare(o2, o1);
	}

	@Override
	public Set<T> supremum(final Set<T> h1, final Set<T> h2) {
		// TODO Auto-generated method stub
		return mPwsLattice.infimum(h1, h2);
	}

	@Override
	public Set<T> infimum(final Set<T> h1, final Set<T> h2) {
		// TODO Auto-generated method stub
		return mPwsLattice.supremum(h1, h2);
	}

}
