/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.Arrays;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;

/**
 * A predicate with multiple locations (used in concurrency analysis) and a list of conjuncts. The conjunction formula
 * is not computed eagerly.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public final class MLPredicateWithConjuncts implements IMLPredicate {
	private final int mSerial;
	private final IcfgLocation[] mProgramPoints;
	private final ImmutableList<IPredicate> mConjuncts;

	/**
	 * Create a new instance from scratch.
	 *
	 * @param serialNumber
	 *            The predicate's serial number
	 * @param programPoints
	 *            The array of locations
	 * @param conjuncts
	 *            The list of conjuncts
	 */
	public MLPredicateWithConjuncts(final int serialNumber, final IcfgLocation[] programPoints,
			final ImmutableList<IPredicate> conjuncts) {
		mSerial = serialNumber;
		mProgramPoints = programPoints;
		mConjuncts = conjuncts;
	}

	/**
	 * Creates a new instance as conjunction of two given predicates.
	 *
	 * @param serialNumber
	 *            The predicate's serial number
	 * @param old
	 *            The first conjunct, which also contains the predicate's locations. May itself be another instance of
	 *            this class.
	 * @param newConjunct
	 *            A new conjunct to be added. Should not be an instance of this class (otherwise, nesting occurs).
	 */
	public MLPredicateWithConjuncts(final int serialNumber, final IMLPredicate old, final IPredicate newConjunct) {
		mSerial = serialNumber;
		mProgramPoints = old.getProgramPoints();

		final ImmutableList<IPredicate> oldConjuncts;
		if (old instanceof MLPredicateWithConjuncts) {
			oldConjuncts = ((MLPredicateWithConjuncts) old).mConjuncts;
		} else {
			oldConjuncts = ImmutableList.singleton(old);
		}
		mConjuncts = new ImmutableList<>(newConjunct, oldConjuncts);
	}

	public ImmutableList<IPredicate> getConjuncts() {
		return mConjuncts;
	}

	@Override
	public int hashCode() {
		return HashUtils.hashJenkins(31, mSerial);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (!(obj instanceof MLPredicateWithConjuncts)) {
			return false;
		}
		final MLPredicateWithConjuncts other = (MLPredicateWithConjuncts) obj;
		return mSerial == other.mSerial;
	}

	@Override
	public Term getFormula() {
		// TODO compute on-demand (and possibly use partial results when constructed from conjunction)
		throw new UnsupportedOperationException();
	}

	@Override
	public Term getClosedFormula() {
		// TODO compute on-demand (and possibly use partial results when constructed from conjunction)
		throw new UnsupportedOperationException();
	}

	@Override
	public String[] getProcedures() {
		// TODO compute on-demand (and possibly use partial results when constructed from conjunction)
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<IProgramVar> getVars() {
		// TODO compute on-demand (and possibly use partial results when constructed from conjunction)
		throw new UnsupportedOperationException();
	}

	@Override
	public IcfgLocation[] getProgramPoints() {
		return mProgramPoints;
	}

	@Override
	public String toString() {
		return mSerial + "#" + Arrays.toString(mProgramPoints) + mConjuncts.toString();
	}
}
