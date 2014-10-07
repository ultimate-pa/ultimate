/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.termination;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;


/**
 * Collects benchmarking information about the termination analysis
 * 
 * @author Matthias Heizmann
 */
public class TerminationAnalysisBenchmark
		implements ICsvProviderProvider<Object> {
	
	private final LBool m_ConstraintsSatisfiability;
	private final int m_VariablesStem;
	private final int m_VariablesLoop;
	private final int m_DisjunctsStem;
	private final int m_DisjunctsLoop;
	private final String m_Template;
	private final int m_Degree;
	private final int m_SupportingInvariants;
	private final int m_MotzkinApplications;
	private final long m_Time;
	
	public TerminationAnalysisBenchmark(
			LBool constraintsSatisfiability, int variablesStem,
			int variablesLoop, int disjunctsStem, int disjunctsLoop,
			String template, int degree, int supportingInvariants,
			int motzkinApplications, long time) {
		m_ConstraintsSatisfiability = constraintsSatisfiability;
		m_VariablesStem = variablesStem;
		m_VariablesLoop = variablesLoop;
		m_DisjunctsStem = disjunctsStem;
		m_DisjunctsLoop = disjunctsLoop;
		m_Template = template;
		m_Degree = degree;
		m_SupportingInvariants = supportingInvariants;
		m_MotzkinApplications = motzkinApplications;
		m_Time = time;
	}
	
	public LBool getConstraintsSatisfiability() {
		return m_ConstraintsSatisfiability;
	}
	
	public int getVariablesStem() {
		return m_VariablesStem;
	}
	
	public int getVariablesLoop() {
		return m_VariablesLoop;
	}
	
	public int getDisjunctsStem() {
		return m_DisjunctsStem;
	}
	
	public int getDisjunctsLoop() {
		return m_DisjunctsLoop;
	}
	
	public String getTemplate() {
		return m_Template;
	}
	
	public int getDegree() {
		return m_Degree;
	}
	
	public int getSupportingInvariants() {
		return m_SupportingInvariants;
	}
	
	public int getMotzkinApplications() {
		return m_MotzkinApplications;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
//			sb.append("Number of variables in the stem: ");
//			sb.append(getVariablesStem());
//			sb.append("  Number of variables in the loop: ");
//			sb.append(getVariablesLoop());
//			sb.append("  Number of disjunctions in the stem: ");
//			sb.append(getDisjunctsStem());
//			sb.append("  Number of disjunctions in the loop: ");
//			sb.append(getDisjunctsLoop());
//			sb.append("  Number of supporting invariants: ");
//			sb.append(getNumSIs());
//			sb.append("  Number of Motzkin applications: ");
//			sb.append(getNumMotzkin());
		for (Entry<String, Object> entry : getKeyValueMap().entrySet()) {
			sb.append(entry.getKey());
			sb.append(": ");
			sb.append(entry.getValue());
			sb.append("  ");
		}
		return sb.toString();
	}
	
	public Map<String, Object> getKeyValueMap() {
		Map<String, Object> result = new LinkedHashMap<String, Object>();
		result.put("Template", m_Template);
		result.put("Degree", m_Degree);
		result.put("ConstraintsSatisfiability", m_ConstraintsSatisfiability);
		result.put("Time", m_Time);
		result.put("VariablesStem", m_VariablesStem);
		result.put("VariablesLoop", m_VariablesLoop);
		result.put("DisjunctsStem", m_DisjunctsStem);
		result.put("DisjunctsLoop", m_DisjunctsLoop);
		result.put("SupportingInvariants", m_SupportingInvariants);
		result.put("MotzkinApplications", m_MotzkinApplications);
		return Collections.unmodifiableMap(result);
	}
	
	@Override
	public ICsvProvider<Object> createCvsProvider() {
		return CsvUtils.constructCvsProviderFromMap(getKeyValueMap());
	}
}