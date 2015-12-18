/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Test Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimatetest.summaries;

import java.io.File;
import java.util.Collection;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.reporting.NewTestSummary;

/**
 * Lists how often a toolchain/setting pair produced a certain result.
 * 
 * @author Matthias Heizmann
 *
 */
public class StandingsSummary extends NewTestSummary {

	public StandingsSummary(
			Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
	}
	
	@Override
	public String getSummaryLog() {
		PartitionedResults pr = getAllResultsPartitioned();
		StringBuilder sb = new StringBuilder();

		{
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = pr.Success;
			String resultCategory = "SUCCESS";
			printStandingsForResultCategory(allOfResultCategory, resultCategory, sb);
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
		}
		
		{
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = pr.Timeout;
			String resultCategory = "TIMEOUT";
			printStandingsForResultCategory(allOfResultCategory, resultCategory, sb);
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
		}

		{
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = pr.Unknown;
			String resultCategory = "UNKNOWN";
			printStandingsForResultCategory(allOfResultCategory, resultCategory, sb);
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
		}

		{
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = pr.Failure;
			String resultCategory = "FAILURE";
			printStandingsForResultCategory(allOfResultCategory, resultCategory, sb);
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
		}

		return sb.toString();
	}

	
	
	private void printStandingsForResultCategory(
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory,
			String resultCategory, StringBuilder sb) {
		sb.append("======= Standings for ").append(resultCategory).append(" =======").append(System.lineSeparator());
		
		HashRelation<TCS, File> tcse2input = new HashRelation<>();
		for (Entry<UltimateRunDefinition, ExtendedResult> result : allOfResultCategory) {
			UltimateRunDefinition urd = result.getKey();
			TCS tcs = new TCS(urd.getToolchain(), urd.getSettings());
			tcse2input.addPair(tcs, urd.getInput());
		}
		
		// sort by TCS strings
		TreeMap<String, Integer> tcs2amount = new TreeMap<>();
		for (TCS tcs : tcse2input.getDomain()) {
			Set<File> inputFiles = tcse2input.getImage(tcs);
			String tcsString = String.valueOf(tcs);
			tcs2amount.put(tcsString, inputFiles.size());
		}
		
		for (Entry<String, Integer> entry : tcs2amount.entrySet()) {
			sb.append(entry.getValue());
			sb.append(" times ");
			sb.append(resultCategory);
			sb.append(" with the ");
			sb.append(entry.getKey());
			sb.append(" toolchain/settings pair.");
			sb.append(System.lineSeparator());
		}
	}

}
