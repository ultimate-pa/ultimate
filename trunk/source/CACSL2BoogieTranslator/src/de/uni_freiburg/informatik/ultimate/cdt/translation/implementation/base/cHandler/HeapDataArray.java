/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Instances of this class define a memory model.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class HeapDataArray {
	private final String m_Name;
	private final ASTType m_ASTType;
	private final int m_Size;
	public HeapDataArray(String name, ASTType aSTType, int size) {
		super();
		m_Name = name;
		m_ASTType = aSTType;
		m_Size = size;
	}
	public String getName() {
		return m_Name;
	}
	public ASTType getASTType() {
		return m_ASTType;
	}
	public String getVariableName() {
		return SFO.MEMORY + "_" + getName();
	}
	public int getSize() {
		return m_Size;
	}
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((m_ASTType == null) ? 0 : m_ASTType.hashCode());
		result = prime * result + ((m_Name == null) ? 0 : m_Name.hashCode());
		result = prime * result + m_Size;
		return result;
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		HeapDataArray other = (HeapDataArray) obj;
		if (m_ASTType == null) {
			if (other.m_ASTType != null)
				return false;
		} else if (!m_ASTType.equals(other.m_ASTType))
			return false;
		if (m_Name == null) {
			if (other.m_Name != null)
				return false;
		} else if (!m_Name.equals(other.m_Name))
			return false;
		if (m_Size != other.m_Size)
			return false;
		return true;
	}
	@Override
	public String toString() {
		return "HeapDataArray [m_Name=" + m_Name + ", m_ASTType=" + m_ASTType + ", m_Size=" + m_Size + "]";
	}
	
	
	
}
