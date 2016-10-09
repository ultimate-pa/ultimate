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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;


/**
 * Constant in a Boogie program.  
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BoogieConst implements IBoogieVar, IProgramConst {
	private final String mIdentifier;
	private final IBoogieType mIType;
	
	/**
	 * TermVariable that represents this constant in {@link TransFormula}s
	 * and {@link IPredicate}s.
	 */
	private final TermVariable mTermVariable;
	
	/**
	 * Constant (0-ary ApplicationTerm) which represents this BoogieVar in
	 * closed SMT terms. 
	 */
	private final ApplicationTerm mSmtConstant;

	/**
	 * 
	 * @param null iff constant belongs to SMT theory
	 */
	public BoogieConst(final String identifier, final IBoogieType iType,
			final TermVariable termVariable, final ApplicationTerm smtConstant) {
		mIdentifier = identifier;
		mIType = iType;
		mTermVariable = termVariable;
		mSmtConstant = smtConstant;
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
	public IBoogieType getIType() {
		return mIType;
	}
	
	@Override
	/**
	 * null iff constant belongs to SMT theory
	 */
	public TermVariable getTermVariable() {
		return mTermVariable;
	}

	@Override
	public ApplicationTerm getDefaultConstant() {
		return mSmtConstant;
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
		final BoogieConst other = (BoogieConst) obj;
		if (mSmtConstant == null) {
			if (other.mSmtConstant != null) {
				return false;
			}
		} else if (!mSmtConstant.equals(other.mSmtConstant)) {
			return false;
		}
		if (mIType == null) {
			if (other.mIType != null) {
				return false;
			}
		} else if (!mIType.equals(other.mIType)) {
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

}
