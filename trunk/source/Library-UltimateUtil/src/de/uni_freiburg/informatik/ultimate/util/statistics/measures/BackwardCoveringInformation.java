/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.statistics.measures;

/**
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BackwardCoveringInformation {

	private final int mPotentialBackwardCoverings;
	private final int mSuccessfullBackwardCoverings;

	public BackwardCoveringInformation() {
		this(0, 0);
	}

	public BackwardCoveringInformation(final int potentialBackwardCoverings, final int successfullBackwardCoverings) {
		mPotentialBackwardCoverings = potentialBackwardCoverings;
		mSuccessfullBackwardCoverings = successfullBackwardCoverings;
	}

	public BackwardCoveringInformation(final BackwardCoveringInformation bci1, final BackwardCoveringInformation bci2) {
		this(bci1.getPotentialBackwardCoverings() + bci2.getPotentialBackwardCoverings(),
				bci1.getSuccessfullBackwardCoverings() + bci2.getSuccessfullBackwardCoverings());
	}

	public int getPotentialBackwardCoverings() {
		return mPotentialBackwardCoverings;
	}

	public int getSuccessfullBackwardCoverings() {
		return mSuccessfullBackwardCoverings;
	}

	@Override
	public String toString() {
		return mSuccessfullBackwardCoverings + "/" + mPotentialBackwardCoverings;
	}

	public boolean isEmpty() {
		return mPotentialBackwardCoverings == 0 && mSuccessfullBackwardCoverings == 0;
	}
}