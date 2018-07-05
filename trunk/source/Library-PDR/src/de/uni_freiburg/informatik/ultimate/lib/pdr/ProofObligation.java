/*
 * Copyright (C) 2018 Jonas Werner (jonaswerner95@gmail.com)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE PDR library .
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PDR library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PDR library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.pdr;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 *
 */
public final class ProofObligation {

	private final IPredicate mToBeBlocked;
	private final IcfgLocation mLocation;
	private final int mLevel;
	private IPredicate mReason;
	private Boolean mHasBeenBlocked;

	/**
	 * Create a new proofobligation, used by pdr.
	 * @param toBeBlocked
	 * 			{@link IPredicate} that needs to be blocked by pdr
	 * @param location
	 * 			{@link IcfgLocation} location where it needs to be blocked
	 * @param level
	 * 			 on which level
	 * @param reason
	 * 			If the proofobligation has been blocked before save the reason why
	 */
	public ProofObligation(final IPredicate toBeBlocked, final IcfgLocation location, final int level,
			final IPredicate reason) {
		mToBeBlocked = toBeBlocked;
		mLocation = location;
		mLevel = level;
		mReason = reason;
		mHasBeenBlocked = false;
	}

	/**
	 * Was the proofobligation blocked before?
	 * @return
	 */
	public Boolean hasBeenBlocked() {
		return mHasBeenBlocked;
	}

	/**
	 * Save a new reason why the proofobligation was blocked
	 * @param newReason
	 */
	public void setReason(final IPredicate newReason) {
		mReason = newReason;
		mHasBeenBlocked = true;
	}

	/**
	 * Get the obligation
	 * @return
	 */
	public IPredicate getToBeBlocked() {
		return mToBeBlocked;
	}

	/**
	 * Get the location
	 * @return
	 */
	public IcfgLocation getLocation() {
		return mLocation;
	}

	/**
	 * Get the level
	 * @return
	 */
	public int getLevel() {
		return mLevel;
	}

	/**
	 * get the reason why it was blockeds
	 * @return
	 */
	public IPredicate getReason() {
		return mReason;
	}

	@Override
	public String toString() {
		return getToBeBlocked().toString() + " at " + getLocation().toString() + " on level -" + getLevel();
	}

}
