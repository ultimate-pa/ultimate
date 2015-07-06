/*
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Model Checker Utils Library.
 *
 * The ULTIMATE Model Checker Utils Library is free software: you can 
 * redistribute it and/or modify it under the terms of the GNU Lesser General 
 * Public License as published by the Free Software Foundation, either 
 * version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Model Checker Utils Library is distributed in the hope that it
 * will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty 
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Model Checker Utils Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Model Checker Utils Library, or any covered work, 
 * by linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE Model Checker Utils Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.model.IType;


/**
 * Constant in a Boogie program.  
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BoogieConst {
	private final String m_Identifier;
	private final IType m_IType;
	
	/**
	 * Constant (0-ary ApplicationTerm) which represents this BoogieVar in
	 * closed SMT terms. 
	 */
	private final ApplicationTerm m_SmtConstant;

	
	
	public BoogieConst(String identifier, IType iType,
			ApplicationTerm smtConstant) {
		m_Identifier = identifier;
		m_IType = iType;
		m_SmtConstant = smtConstant;
	}
	
	
	public String getIdentifier() {
		return m_Identifier;
	}

	public IType getIType() {
		return m_IType;
	}


	public ApplicationTerm getSmtConstant() {
		return m_SmtConstant;
	}


	@Override
	public int hashCode() {
		return m_Identifier.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		BoogieConst other = (BoogieConst) obj;
		if (m_SmtConstant == null) {
			if (other.m_SmtConstant != null)
				return false;
		} else if (!m_SmtConstant.equals(other.m_SmtConstant))
			return false;
		if (m_IType == null) {
			if (other.m_IType != null)
				return false;
		} else if (!m_IType.equals(other.m_IType))
			return false;
		if (m_Identifier == null) {
			if (other.m_Identifier != null)
				return false;
		} else if (!m_Identifier.equals(other.m_Identifier))
			return false;
		return true;
	}
}
