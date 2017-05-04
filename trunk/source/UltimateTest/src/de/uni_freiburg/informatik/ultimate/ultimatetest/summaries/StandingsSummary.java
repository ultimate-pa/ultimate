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
package de.uni_freiburg.informatik.ultimate.ultimatetest.summaries;

import java.util.Collection;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.reporting.ExtendedResult;
import de.uni_freiburg.informatik.ultimate.test.reporting.BaseTestSummary;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Lists how often a toolchain/setting pair produced a certain result.
 * 
 * @author Matthias Heizmann
 *
 */
public class StandingsSummary extends BaseTestSummary {

	public StandingsSummary(
			Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
	}
	
	@Override
	public String getLog() {
		final PartitionedResults pr = getAllResultsPartitioned();
		final StringBuilder sb = new StringBuilder();

		{
			final Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = pr.Success;
			final String resultCategory = "SUCCESS";
			printStandingsForResultCategory(allOfResultCategory, resultCategory, sb);
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
		}
		
		{
			final Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = pr.Timeout;
			final String resultCategory = "TIMEOUT";
			printStandingsForResultCategory(allOfResultCategory, resultCategory, sb);
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
		}

		{
			final Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = pr.Unknown;
			final String resultCategory = "UNKNOWN";
			printStandingsForResultCategory(allOfResultCategory, resultCategory, sb);
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
		}

		{
			final Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = pr.Failure;
			final String resultCategory = "FAILURE";
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
		
		final HashRelation<TCS, String> tcse2input = new HashRelation<>();
		for (final Entry<UltimateRunDefinition, ExtendedResult> result : allOfResultCategory) {
			final UltimateRunDefinition urd = result.getKey();
			final TCS tcs = new TCS(urd.getToolchain(), urd.getSettings());
			tcse2input.addPair(tcs, urd.getInputFileNames());
		}
		
		// sort by TCS strings
		final TreeMap<String, Integer> tcs2amount = new TreeMap<>();
		for (final TCS tcs : tcse2input.getDomain()) {
			final Set<String> inputFiles = tcse2input.getImage(tcs);
			final String tcsString = String.valueOf(tcs);
			tcs2amount.put(tcsString, inputFiles.size());
		}
		
		for (final Entry<String, Integer> entry : tcs2amount.entrySet()) {
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
