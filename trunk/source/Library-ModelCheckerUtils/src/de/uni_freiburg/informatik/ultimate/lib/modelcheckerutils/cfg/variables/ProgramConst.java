/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Default implementation of {@link IProgramConst}.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class ProgramConst extends ProgramFunction implements IProgramConst {
	private static final long serialVersionUID = 2529175722580437047L;

	private final String mIdentifier;
	/**
	 * @deprecated SMT constants that below to the theory are no {@link IProgramConst}s
	 */
	@Deprecated
	private final boolean mBelongsToSmtTheory;

	/**
	 * Constant (0-ary ApplicationTerm) which represents this ProgramConst in closed SMT terms.
	 */
	private final ApplicationTerm mSmtConstant;

	/**
	 *
	 * @param belongsToSmtTheory
	 *            iff constant belongs to SMT theory
	 */
	public ProgramConst(final String identifier, final ApplicationTerm smtConstant, final boolean belongsToSmtTheory) {
		super(smtConstant.getFunction());
		mIdentifier = identifier;
		mSmtConstant = smtConstant;
		mBelongsToSmtTheory = belongsToSmtTheory;
	}

	@Override
	public String getIdentifier() {
		return mIdentifier;
	}

	@Override
	public String getGloballyUniqueId() {
		return getIdentifier();
	}

	@Override
	public Term getTerm() {
		return getDefaultConstant();
	}

	@Override
	public ApplicationTerm getDefaultConstant() {
		return mSmtConstant;
	}

	public boolean belongsToSmtTheory() {
		return mBelongsToSmtTheory;
	}

	@Override
	public int hashCode() {
		return mIdentifier.hashCode();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final ProgramConst other = (ProgramConst) obj;
		if (mSmtConstant == null) {
			if (other.mSmtConstant != null) {
				return false;
			}
		} else if (!mSmtConstant.equals(other.mSmtConstant)) {
			return false;
		}
		if (mIdentifier == null) {
			if (other.mIdentifier != null) {
				return false;
			}
		} else if (!mIdentifier.equals(other.mIdentifier)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return mIdentifier;
	}

	@Override
	public Sort getSort() {
		return getTerm().getSort();
	}

	@Override
	public boolean isGlobal() {
		return true;
	}

}
