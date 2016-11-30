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

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.reporting.BaseTestSummary;
import de.uni_freiburg.informatik.ultimate.test.reporting.ExtendedResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * List which toolchain/setting pair combinations are the only ones that produced a certain result.
 * 
 * @author Matthias Heizmann
 */
public class KingOfTheHillSummary extends BaseTestSummary {
	/**
	 * @param ultimateTestSuite
	 *            Ultimate test suite.
	 */
	public KingOfTheHillSummary(final Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
	}
	
	@Override
	public String getSummaryLog() {
		final PartitionedResults pr = getAllResultsPartitioned();
		final StringBuilder builder = new StringBuilder();
		
		printSuccess(pr, builder);
		
		printTimeout(pr, builder);
		
		printUnknown(pr, builder);
		
		printFailure(pr, builder);
		
		return builder.toString();
	}
	
	private void printSuccess(final PartitionedResults partRes, final StringBuilder builder) {
		final Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = partRes.Success;
		final String resultCategory = "SUCCESS";
		printCategory(builder, allOfResultCategory, resultCategory);
	}
	
	private void printTimeout(final PartitionedResults partRes, final StringBuilder builder) {
		final Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = partRes.Timeout;
		final String resultCategory = "TIMEOUT";
		printCategory(builder, allOfResultCategory, resultCategory);
	}
	
	private void printUnknown(final PartitionedResults partRes, final StringBuilder builder) {
		final Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = partRes.Unknown;
		final String resultCategory = "UNKNOWN";
		printCategory(builder, allOfResultCategory, resultCategory);
	}
	
	private void printFailure(final PartitionedResults partRes, final StringBuilder builder) {
		final Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory = partRes.Failure;
		final String resultCategory = "FAILURE";
		printCategory(builder, allOfResultCategory, resultCategory);
	}
	
	private void printCategory(final StringBuilder builder,
			final Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory,
			final String resultCategory) {
		printKingOfTheHillForResultCategory(allOfResultCategory, resultCategory, builder);
		builder.append(System.lineSeparator());
		builder.append(System.lineSeparator());
		builder.append(System.lineSeparator());
		builder.append(System.lineSeparator());
	}
	
	private void printKingOfTheHillForResultCategory(
			final Collection<Entry<UltimateRunDefinition, ExtendedResult>> allOfResultCategory,
			final String resultCategory, final StringBuilder builder) {
		builder.append("======= King of the Hill for ").append(resultCategory).append(" =======")
				.append(System.lineSeparator());
		
		final HashRelation<String, TCS> input2tcses = new HashRelation<>();
		for (final Entry<UltimateRunDefinition, ExtendedResult> result : allOfResultCategory) {
			final UltimateRunDefinition urd = result.getKey();
			final TCS tcs = new TCS(urd.getToolchain(), urd.getSettings());
			input2tcses.addPair(urd.getInputFileNames(), tcs);
		}
		final HashRelation<Set<TCS>, String> tcses2input = new HashRelation<>();
		for (final String input : input2tcses.getDomain()) {
			final Set<TCS> tcses = input2tcses.getImage(input);
			tcses2input.addPair(tcses, input);
		}
		final Comparator<Set<TCS>> comp = (arg0, arg1) -> arg0.size() - arg1.size();
		final Set<TCS>[] tcsPowerset =
				(Set<TCS>[]) tcses2input.getDomain().toArray(new Set<?>[tcses2input.getDomain().size()]);
		
		Arrays.sort(tcsPowerset, comp);
		for (final Set<TCS> tcses : tcsPowerset) {
			builder.append("The " + tcses.size() + " toolchain/settings pairs").append(System.lineSeparator());
			for (final TCS tcs : tcses) {
				builder.append("    ").append(tcs).append(System.lineSeparator());
			}
			final Set<String> inputFiles = tcses2input.getImage(tcses);
			builder.append("are exactly the pairs where the result was ");
			builder.append(resultCategory);
			builder.append(" on the following ");
			builder.append(inputFiles.size());
			builder.append(" files").append(System.lineSeparator());
			for (final String file : inputFiles) {
				builder.append("  ").append(file).append(System.lineSeparator());
			}
			builder.append(System.lineSeparator());
		}
	}
}
