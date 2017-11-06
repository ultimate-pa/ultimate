/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
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
 * Collects benchmarking information about the nontermination analysis
 * 
 * @author Matthias Heizmann
 */
public class NonterminationAnalysisBenchmark
		implements ICsvProviderProvider<Object> {
	
	// column headers of the resulting csv
	public static final String s_Label_ConstraintsSatisfiability = "ConstraintsSatisfiability";
	public static final String s_Label_IsFixpoint = "IsFixpoint";
	public static final String s_Label_Time = "Time";
	public static final String s_Label_VariablesStem = "VariablesStem";
	public static final String s_Label_VariablesLoop = "VariablesLoop";
	public static final String s_Label_DisjunctsStem = "DisjunctsStem";
	public static final String s_Label_DisjunctsLoop = "DisjunctsLoop";
	
	private final LBool mConstraintsSatisfiability;
	private final boolean mIsFixpoint;
	private final int mVariablesStem;
	private final int mVariablesLoop;
	private final int mDisjunctsStem;
	private final int mDisjunctsLoop;
	private final long mTime;
	
	public NonterminationAnalysisBenchmark(
			final LBool constraintsSatisfiability, final boolean isFixpoint, final int variablesStem,
			final int variablesLoop, final int disjunctsStem, final int disjunctsLoop,
			final long time) {
		mConstraintsSatisfiability = constraintsSatisfiability;
		mIsFixpoint = isFixpoint;
		mVariablesStem = variablesStem;
		mVariablesLoop = variablesLoop;
		mDisjunctsStem = disjunctsStem;
		mDisjunctsLoop = disjunctsLoop;
		mTime = time;
	}
	
	public LBool getConstraintsSatisfiability() {
		return mConstraintsSatisfiability;
	}
	
	public boolean isFixpoint() {
		return mIsFixpoint;
	}

	public int getVariablesStem() {
		return mVariablesStem;
	}
	
	public int getVariablesLoop() {
		return mVariablesLoop;
	}
	
	public int getDisjunctsStem() {
		return mDisjunctsStem;
	}
	
	public int getDisjunctsLoop() {
		return mDisjunctsLoop;
	}
	
	public long getTime() {
		return mTime;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
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
		for (final Entry<String, Object> entry : getKeyValueMap().entrySet()) {
			sb.append(entry.getKey());
			sb.append(": ");
			sb.append(entry.getValue());
			sb.append("  ");
		}
		return sb.toString();
	}
	
	public Map<String, Object> getKeyValueMap() {
		final Map<String, Object> result = new LinkedHashMap<String, Object>();
		result.put(s_Label_ConstraintsSatisfiability, mConstraintsSatisfiability);
		result.put(s_Label_IsFixpoint, mIsFixpoint);
		result.put(s_Label_Time, mTime);
		result.put(s_Label_VariablesStem, mVariablesStem);
		result.put(s_Label_VariablesLoop, mVariablesLoop);
		result.put(s_Label_DisjunctsStem, mDisjunctsStem);
		result.put(s_Label_DisjunctsLoop, mDisjunctsLoop);
		return Collections.unmodifiableMap(result);
	}
	

	
	
	@Override
	public ICsvProvider<Object> createCsvProvider() {
		return CsvUtils.constructCvsProviderFromMap(getKeyValueMap());
	}
}
