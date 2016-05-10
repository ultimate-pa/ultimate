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

import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.relation.HashRelation;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.reporting.ExtendedResult;
import de.uni_freiburg.informatik.ultimatetest.reporting.NewTestSummary;

/**
 * List which toolchain/setting pair combinations are the only ones that 
 * produced a certain result.
 * 
 * @author Matthias Heizmann
 *
 */
public class KingOfTheHillSummary extends NewTestSummary {

	public KingOfTheHillSummary(
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
			printKingOfTheHillForResultCategory(allOfResultCategory, resultCategory, sb);
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
		}
		
		{
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = pr.Timeout;
			String resultCategory = "TIMEOUT";
			printKingOfTheHillForResultCategory(allOfResultCategory, resultCategory, sb);
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
		}

		{
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = pr.Unknown;
			String resultCategory = "UNKNOWN";
			printKingOfTheHillForResultCategory(allOfResultCategory, resultCategory, sb);
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
		}

		{
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = pr.Failure;
			String resultCategory = "FAILURE";
			printKingOfTheHillForResultCategory(allOfResultCategory, resultCategory, sb);
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
			sb.append(System.lineSeparator());
		}

		return sb.toString();
	}

	
	
	private void printKingOfTheHillForResultCategory(
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory,
			String resultCategory, StringBuilder sb) {
		sb.append("======= King of the Hill for ").append(resultCategory).append(" =======").append(System.lineSeparator());
		
		HashRelation<String, TCS> input2tcses = new HashRelation<>();
		for (Entry<UltimateRunDefinition, ExtendedResult> result : allOfResultCategory) {
			UltimateRunDefinition urd = result.getKey();
			TCS tcs = new TCS(urd.getToolchain(), urd.getSettings());
			input2tcses.addPair(urd.getInputFileNames(), tcs);
		}
		HashRelation<Set<TCS>, String> tcses2input = new HashRelation<>();
		for (String input : input2tcses.getDomain()) {
			Set<TCS> tcses = input2tcses.getImage(input);
			tcses2input.addPair(tcses, input);
		}
		Set<TCS>[] tcsPowerset = (Set<TCS>[]) tcses2input.getDomain().toArray(new Set<?>[tcses2input.getDomain().size()]);
		Comparator<Set<TCS>> comp = new Comparator<Set<TCS>>() {

			@Override
			public int compare(Set<TCS> arg0, Set<TCS> arg1) {
				return arg0.size() - arg1.size();
			}
		};
		
		Arrays.sort(tcsPowerset, comp);
		for (Set<TCS> tcses : tcsPowerset) {
			sb.append("The " + tcses.size() + " toolchain/settings pairs").append(System.lineSeparator());
			for (TCS tcs : tcses) {
				sb.append("    ").append(tcs).append(System.lineSeparator());
			}
			Set<String> inputFiles = tcses2input.getImage(tcses);
			sb.append("are exactly the pairs were the result was "); 
			sb.append(resultCategory);
			sb.append(" on the following ");
			sb.append(inputFiles.size());
			sb.append(" files").append(System.lineSeparator());
			for (String file : inputFiles) {
				sb.append("  ").append(file).append(System.lineSeparator());
			}
			sb.append(System.lineSeparator());
		}
	}

}
