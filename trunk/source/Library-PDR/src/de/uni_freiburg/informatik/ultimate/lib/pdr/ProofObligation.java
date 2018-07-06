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

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 *
 */
public final class ProofObligation {

	private final IPredicate mToBeBlocked;
	private final IcfgLocation mLocation;
	private final int mLevel;
	private final List<Triple<IPredicate, IAction, IPredicate>> mBlockedQueries;

	/**
	 * Create a new proofobligation, used by pdr.
	 * 
	 * @param toBeBlocked
	 *            {@link IPredicate} that needs to be blocked by pdr
	 * @param location
	 *            {@link IcfgLocation} location where it needs to be blocked
	 * @param level
	 *            on which level
	 * @param reason
	 *            If the proofobligation has been blocked before save the reason why
	 */
	public ProofObligation(final IPredicate toBeBlocked, final IcfgLocation location, final int level) {
		mToBeBlocked = toBeBlocked;
		mLocation = location;
		mLevel = level;
		mBlockedQueries = new ArrayList<>();
	}

	/**
	 * If a query to the SMT-solver has already been seen and blocked, take its toBeBlocked and add it to the
	 * corresponding frame.
	 * 
	 * @param blockedQuery
	 */
	public final void addBlockedQuery(final Triple<IPredicate, IAction, IPredicate> blockedQuery) {
		mBlockedQueries.add(blockedQuery);
	}

	/**
	 * Get the obligation
	 * 
	 * @return
	 */
	public final IPredicate getToBeBlocked() {
		return mToBeBlocked;
	}

	/**
	 * Get the location
	 * 
	 * @return
	 */
	public final IcfgLocation getLocation() {
		return mLocation;
	}

	/**
	 * Get the level
	 * 
	 * @return
	 */
	public final int getLevel() {
		return mLevel;
	}

	/**
	 * Get the queries to the SMT-solver that have already been blocked.
	 * 
	 * @return
	 */
	public final List<Triple<IPredicate, IAction, IPredicate>> getBlockedQueries() {
		return mBlockedQueries;
	}

	@Override
	public final String toString() {
		return getToBeBlocked().toString() + " at " + getLocation().toString() + " on level -" + getLevel();
	}

}
