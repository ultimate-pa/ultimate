/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

public class PredicateWithHistory extends SPredicate {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 4545005036147569544L;
	private final Map<Integer,Term> mHistory;
	

	protected PredicateWithHistory(BoogieIcfgLocation programPoint, int serialNumber, 
			String[] procedures, Term formula,
			Set<IProgramVar> vars, Term closedFormula, Map<Integer,Term> history) {
		super(programPoint, serialNumber, procedures, formula, vars, closedFormula);
		mHistory = history;
	}

	/**
	 * The published attributes.  Update this and getFieldValue()
	 * if you add new attributes.
	 */
	private final static String[] s_AttribFields = {
		"ProgramPoint", "Procedures", "Formula", "Vars", "History"
	};
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}
	
	@Override
	protected Object getFieldValue(String field) {
		if (field == "History") {
			return mHistory;
		} else {
			return super.getFieldValue(field);
		}
	}
	
	public Map<Integer,Term> getCopyOfHistory() {
		final Map<Integer,Term> result = new HashMap<Integer,Term>();
		for (final Integer i : mHistory.keySet()) {
			result.put(i, mHistory.get(i));
		}
		return result;
	}
	
//	public void setHistory(Map<Integer,Term> history) {
//		mHistory = history;
//	}

}
