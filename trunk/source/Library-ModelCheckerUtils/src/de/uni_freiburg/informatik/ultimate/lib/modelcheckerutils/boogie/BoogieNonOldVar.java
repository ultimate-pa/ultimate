/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * See comment in GlobalBoogieVar.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BoogieNonOldVar extends GlobalBoogieVar implements IProgramNonOldVar {

	private static final long serialVersionUID = 103072739646531062L;

	private final int mHashCode;
	private final BoogieOldVar mOldVar;

	public BoogieNonOldVar(final String identifier, final IBoogieType iType, final TermVariable tv,
			final ApplicationTerm defaultConstant, final ApplicationTerm primedConstant, final BoogieOldVar oldVar) {
		super(identifier, iType, tv, defaultConstant, primedConstant);
		mOldVar = oldVar;
		mHashCode = computeHashCode();
	}

	@Override
	public String getGloballyUniqueId() {
		return IProgramNonOldVar.super.getGloballyUniqueId();
	}

	@Override
	public String getIdentifier() {
		return mIdentifier;
	}

	@Override
	public BoogieOldVar getOldVar() {
		return mOldVar;
	}

	private int computeHashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((getIdentifier() == null) ? 0 : getIdentifier().hashCode());
		result = prime * result + ((getProcedure() == null) ? 0 : getProcedure().hashCode());
		return result;
	}

	@Override
	public int hashCode() {
		return mHashCode;
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
		final IProgramNonOldVar other = (IProgramNonOldVar) obj;
		if (getIdentifier() == null) {
			if (other.getIdentifier() != null) {
				return false;
			}
		} else if (!getIdentifier().equals(other.getIdentifier())) {
			return false;
		}
		if (isOldvar() != other.isOldvar()) {
			return false;
		}
		if (getProcedure() == null) {
			if (other.getProcedure() != null) {
				return false;
			}
		} else if (!getProcedure().equals(other.getProcedure())) {
			return false;
		}
		return true;
	}
}
