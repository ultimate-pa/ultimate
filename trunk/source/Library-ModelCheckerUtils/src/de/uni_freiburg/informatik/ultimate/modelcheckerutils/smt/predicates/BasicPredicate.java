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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BasicPredicate extends AbstractAnnotations implements IPredicate {
	private static final long serialVersionUID = -2257982001512157622L;
	protected final String[] m_Procedures;
	protected Term m_Formula;
	protected final Term m_ClosedFormula;
	protected final Set<BoogieVar> m_Vars;
	protected final int m_SerialNumber;
	
	
	
	public BasicPredicate(int serialNumber, String[] procedures, Term term, Set<BoogieVar> vars,
			Term closedFormula) {
		m_Formula = term;
		m_ClosedFormula = closedFormula;
		m_Procedures = procedures;
		m_Vars = vars;
		m_SerialNumber = serialNumber;
	}


	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"Procedures", "Formula", "Vars"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field.equals("Procedures"))
			return m_Procedures;
		else if (field.equals("Formula"))
			return m_Formula;
		else if (field.equals("Vars"))
			return m_Vars;
		else
			throw new UnsupportedOperationException("Unknown field "+field);
	}
	
	
	public String[] getProcedures() {
		return m_Procedures;
	}

	/**
	 * @return the m_Assertion
	 */
	public Term getFormula() {
		return m_Formula;
	}
	
	public Term getClosedFormula() {
		return m_ClosedFormula;
	}

	public Set<BoogieVar> getVars() {
		return m_Vars;
	}
	
	@Override
	public String toString() {
		String result = m_SerialNumber + "#";
		result += m_Formula.toStringDirect();
		return result;
	}

	public boolean isUnknown() {
		return false;
	}

	@Override
	public int hashCode() {
		return m_SerialNumber;
	}
	
}