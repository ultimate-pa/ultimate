/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.model.boogie;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.IType;

/**
 * Variable in a boogie program. The procedure field of global variables is null.
 * Only global variables can be old variables. Two BoogieVars are equivalent if 
 * they have the same identifier, same procedure, same old-flag. Equivalence
 * does not depend on the IType. We expect that two equivalent BoogieVars with
 * different ITypes never occur in the same program. 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public abstract class BoogieVar implements Serializable {

	private static final long serialVersionUID = 103072739646531062L;
	private final String m_Identifier;
	private final IType m_IType;
	
	/**
	 * TermVariable which represents this BoogieVar in SMT terms.
	 */
	private final TermVariable m_TermVariable;
	
	/**
	 * Constant (0-ary ApplicationTerm) which represents this BoogieVar in
	 * closed SMT terms. 
	 */
	private final ApplicationTerm m_DefaultConstant;

	/**
	 * Constant (0-ary ApplicationTerm) which represents this BoogieVar if it
	 * occurs as next state variable in closed SMT which describe a transition. 
	 */
	private final ApplicationTerm m_PrimedConstant;

	
	public BoogieVar(String identifier, IType iType, 
			TermVariable tv,
			ApplicationTerm defaultConstant,
			ApplicationTerm primedContant) {
		m_Identifier = identifier;
		m_IType = iType;
		m_TermVariable = tv;
		m_DefaultConstant = defaultConstant;
		m_PrimedConstant = primedContant;
	}
	
	
	
	public String getIdentifier() {
		return m_Identifier;
	}
	
	/**
	 * Returns the procedure in which this variable was declared. If this a 
	 * global variable, then null is returned.
	 */
	public abstract String getProcedure();
	
	public IType getIType() {
		return m_IType;
	}
	public abstract boolean isGlobal();
	
	public abstract boolean isOldvar();
	
	public TermVariable getTermVariable() {
		assert m_TermVariable != null;
		return m_TermVariable;
	}


	public ApplicationTerm getDefaultConstant() {
		return m_DefaultConstant;
	}


	public ApplicationTerm getPrimedConstant() {
		return m_PrimedConstant;
	}


	/**
	 * Returns an identifier that is globally unique. If this is global non-old
	 * we return the identifier, if this is global oldvar we add old(.), if
	 * this is local we add the procedure name as prefix.
	 */
	public String getGloballyUniqueId() {
		if (isGlobal()) {
			if (isOldvar()) {
				return "old(" + getIdentifier()+")";
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
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		BoogieVar other = (BoogieVar) obj;
		if (getIdentifier() == null) {
			if (other.getIdentifier() != null)
				return false;
		} else if (!getIdentifier().equals(other.getIdentifier()))
			return false;
		if (isOldvar() != other.isOldvar())
			return false;
		if (getProcedure() == null) {
			if (other.getProcedure() != null)
				return false;
		} else if (!getProcedure().equals(other.getProcedure()))
			return false;
		return true;
	}
	

	

}
