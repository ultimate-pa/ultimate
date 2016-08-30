/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * Variable in a boogie program. The procedure field of global variables is null. Only global variables can be old
 * variables. Two BoogieVars are equivalent if they have the same identifier, same procedure, same old-flag. Equivalence
 * does not depend on the IType. We expect that two equivalent BoogieVars with different ITypes never occur in the same
 * program.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public abstract class BoogieVar implements IProgramVar, Serializable, IBoogieVar {

	private static final long serialVersionUID = 103072739646531062L;
	private final String mIdentifier;
	private final IBoogieType mIType;

	/**
	 * TermVariable which represents this BoogieVar in SMT terms.
	 */
	private final TermVariable mTermVariable;

	/**
	 * Constant (0-ary ApplicationTerm) which represents this BoogieVar in closed SMT terms.
	 */
	private final ApplicationTerm mDefaultConstant;

	/**
	 * Constant (0-ary ApplicationTerm) which represents this BoogieVar if it occurs as next state variable in closed
	 * SMT which describe a transition.
	 */
	private final ApplicationTerm mPrimedConstant;

	public BoogieVar(final String identifier, final IBoogieType iType, final TermVariable tv,
			final ApplicationTerm defaultConstant, final ApplicationTerm primedContant) {
		mIdentifier = identifier;
		mIType = iType;
		mTermVariable = tv;
		mDefaultConstant = defaultConstant;
		mPrimedConstant = primedContant;
	}

	@Override
	public String getIdentifier() {
		return mIdentifier;
	}

	/**
	 * Returns the procedure in which this variable was declared. If this a global variable, then null is returned.
	 */
	@Override
	public abstract String getProcedure();

	@Override
	public IBoogieType getIType() {
		return mIType;
	}

	@Override
	public abstract boolean isGlobal();

	@Override
	public abstract boolean isOldvar();

	@Override
	public TermVariable getTermVariable() {
		assert mTermVariable != null;
		return mTermVariable;
	}

	@Override
	public ApplicationTerm getDefaultConstant() {
		return mDefaultConstant;
	}

	@Override
	public ApplicationTerm getPrimedConstant() {
		return mPrimedConstant;
	}

	/**
	 * Returns an identifier that is globally unique. If this is global non-old we return the identifier, if this is
	 * global oldvar we add old(.), if this is local we add the procedure name as prefix.
	 */
	@Override
	public String getGloballyUniqueId() {
		if (isGlobal()) {
			if (isOldvar()) {
				return "old(" + getIdentifier() + ")";
			} else {
				return getIdentifier();
			}
		} else {
			return getProcedure() + "_" + getIdentifier();
		}
	}

	@Override
	public String toString() {
		return getGloballyUniqueId();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (isOldvar() ? 1231 : 1237);
		result = prime * result + ((getIdentifier() == null) ? 0 : getIdentifier().hashCode());
		result = prime * result + ((getProcedure() == null) ? 0 : getProcedure().hashCode());
		return result;
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
		final BoogieVar other = (BoogieVar) obj;
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
