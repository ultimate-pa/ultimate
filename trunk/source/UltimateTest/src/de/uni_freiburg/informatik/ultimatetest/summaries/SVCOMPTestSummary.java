/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimate.test.reporting.BaseTestSummary;
import de.uni_freiburg.informatik.ultimate.test.reporting.ExtendedResult;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimatetest.suites.svcomp.SVCOMP15TestSuite;

/**
 * This summary should only be used with {@link SVCOMP15TestSuite}, because it relies on the name of the test case
 * generated there to extract the SVCOMP category of a given test.
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class SVCOMPTestSummary extends BaseTestSummary {

	public SVCOMPTestSummary(final Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
	}

	@Override
	public String getSummaryLog() {

		final Set<TCS> tcs = CoreUtil.selectDistinct(mResults.entrySet(), new IMyReduce<TCS>() {
			@Override
			public TCS reduce(final Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return new TCS(entry.getKey().getToolchain(), entry.getKey().getSettings());
			}
		});

		final Set<String> svcompCategories = CoreUtil.selectDistinct(mResults.entrySet(), new IMyReduce<String>() {
			@Override
			public String reduce(final Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getValue().getTestname().split(" ")[0];
			}
		});

		final StringBuilder sb = new StringBuilder();
		final String indent = "\t";
		for (final TCS atcs : tcs) {
			for (final String svcompCategory : svcompCategories) {
				final Collection<Entry<UltimateRunDefinition, ExtendedResult>> results =
						CoreUtil.where(mResults.entrySet(), new ITestSummaryResultPredicate() {
							@Override
							public boolean test(final Entry<UltimateRunDefinition, ExtendedResult> entry) {
								return entry.getKey().getToolchain().equals(atcs.Toolchain)
										&& entry.getKey().getSettings().equals(atcs.Setting)
										&& entry.getValue().getTestname().split(" ")[0].equals(svcompCategory);
							}
						});

				if (results.isEmpty()) {
					continue;
				}
				// write the name
				sb.append("################# ");
				sb.append(atcs.Toolchain.getName());
				sb.append(" ");
				sb.append(atcs.Setting.getName());
				sb.append(" ");
				sb.append(svcompCategory);
				sb.append(" #################");
				sb.append(CoreUtil.getPlatformLineSeparator());

				final StringBuilder summary = new StringBuilder();
				int totalCount = 0;
				// write the result type and the content (SUCCESS, UNKNOWN,
				// FAIL)
				for (final TestResult tResult : TestResult.values()) {
					final Collection<Entry<UltimateRunDefinition, ExtendedResult>> specificResults =
							CoreUtil.where(results, new ITestSummaryResultPredicate() {
								@Override
								public boolean test(final Entry<UltimateRunDefinition, ExtendedResult> entry) {
									return entry.getValue().getResult() == tResult;
								}
							});

					summary.append(tResult).append(": ").append(specificResults.size())
							.append(CoreUtil.getPlatformLineSeparator());

					if (specificResults.isEmpty()) {
						continue;
					}
					totalCount += specificResults.size();

					sb.append("===== ");
					sb.append(tResult);
					sb.append(" =====").append(CoreUtil.getPlatformLineSeparator());

					final Set<String> resultCategories =
							CoreUtil.selectDistinct(specificResults, new IMyReduce<String>() {
								@Override
								public String reduce(final Entry<UltimateRunDefinition, ExtendedResult> entry) {
									return entry.getValue().getCategory();
								}
							});

					for (final String resultCategory : resultCategories) {
						// group by result category
						sb.append(indent).append(resultCategory).append(CoreUtil.getPlatformLineSeparator());
						final Collection<Entry<UltimateRunDefinition, ExtendedResult>> resultsByCategory =
								CoreUtil.where(results, new ITestSummaryResultPredicate() {
									@Override
									public boolean test(final Entry<UltimateRunDefinition, ExtendedResult> entry) {
										return entry.getValue().getCategory().equals(resultCategory);
									}
								});
						for (final Entry<UltimateRunDefinition, ExtendedResult> entry : resultsByCategory) {

							// name of the file
							sb.append(indent).append(indent);
							sb.append(entry.getKey().getInputFileNames());
							sb.append(CoreUtil.getPlatformLineSeparator());

							// message
							sb.append(indent).append(indent).append(indent).append(entry.getValue().getMessage())
									.append(CoreUtil.getPlatformLineSeparator());

						}

						sb.append(indent).append("Total: ").append(resultsByCategory.size())
								.append(CoreUtil.getPlatformLineSeparator());
						sb.append(CoreUtil.getPlatformLineSeparator());
					}
					sb.append(CoreUtil.getPlatformLineSeparator());
				}

				sb.append("===== TOTAL =====").append(CoreUtil.getPlatformLineSeparator());
				sb.append(summary.toString());
				sb.append("All: ").append(totalCount).append(CoreUtil.getPlatformLineSeparator());
				sb.append(CoreUtil.getPlatformLineSeparator());
			}

		}

		final HashMap<String, Integer> nemesisMap = new HashMap<>();
		for (final Entry<UltimateRunDefinition, ExtendedResult> entry : mResults.entrySet()) {
			if (entry.getValue().getResult().equals(TestResult.SUCCESS)) {
				continue;
			}

			final String message = entry.getValue().getMessage().intern();
			if (!nemesisMap.containsKey(message)) {
				nemesisMap.put(message, 1);
			} else {
				nemesisMap.put(message, nemesisMap.get(message) + 1);
			}
		}

		final List<Entry<String, Integer>> nemesis = new ArrayList<>(nemesisMap.entrySet());
		Collections.sort(nemesis, new Comparator<Entry<String, Integer>>() {
			@Override
			public int compare(final Entry<String, Integer> o1, final Entry<String, Integer> o2) {
				return -o1.getValue().compareTo(o2.getValue());
			}
		});

		sb.append("################# Reasons for !SUCCESS #################")
				.append(CoreUtil.getPlatformLineSeparator());
		for (final Entry<String, Integer> entry : nemesis) {
			sb.append(entry.getValue()).append(indent).append(entry.getKey())
					.append(CoreUtil.getPlatformLineSeparator());
		}
		sb.append(CoreUtil.getPlatformLineSeparator());

		sb.append("################# Total Comparison #################").append(CoreUtil.getPlatformLineSeparator());
		sb.append("Toolchain").append(indent);
		sb.append("Settings").append(indent);
		sb.append("Success").append(indent);
		sb.append("Unknown").append(indent);
		sb.append("Fail").append(indent);
		sb.append(CoreUtil.getPlatformLineSeparator());
		for (final TCS toolchainAndSettings : tcs) {
			final Collection<Entry<UltimateRunDefinition, ExtendedResult>> specificResults =
					CoreUtil.where(mResults.entrySet(), new ITestSummaryResultPredicate() {
						@Override
						public boolean test(final Entry<UltimateRunDefinition, ExtendedResult> entry) {
							return entry.getKey().getToolchain().equals(toolchainAndSettings.Toolchain)
									&& entry.getKey().getSettings().equals(toolchainAndSettings.Setting);
						}
					});
			appendComparison(sb, indent, toolchainAndSettings, specificResults);
		}

		sb.append(CoreUtil.getPlatformLineSeparator());
		sb.append("################# Comparison by SVCOMP Category #################")
				.append(CoreUtil.getPlatformLineSeparator());

		sb.append("SVCOMP-Cat.").append(indent);
		sb.append("Toolchain").append(indent);
		sb.append("Settings").append(indent);
		sb.append("Success").append(indent);
		sb.append("Unknown").append(indent);
		sb.append("Fail").append(indent);
		sb.append(CoreUtil.getPlatformLineSeparator());
		for (final TCS toolchainAndSettings : tcs) {
			for (final String svcompCategory : svcompCategories) {
				final Collection<Entry<UltimateRunDefinition, ExtendedResult>> specificResults =
						mResults.entrySet().stream()
								.filter(entry -> entry.getKey().getToolchain().equals(toolchainAndSettings.Toolchain)
										&& entry.getKey().getSettings().equals(toolchainAndSettings.Setting)
										&& entry.getValue().getTestname().split(" ")[0].equals(svcompCategory))
								.collect(Collectors.toList());
				sb.append(svcompCategory).append(indent);
				appendComparison(sb, indent, toolchainAndSettings, specificResults);
			}

		}

		return sb.toString();
	}

	private static void appendComparison(final StringBuilder sb, final String indent, final TCS toolchainAndSettings,
			final Collection<Entry<UltimateRunDefinition, ExtendedResult>> specificResults) {

		final long success =
				specificResults.stream().filter(a -> a.getValue().getResult().equals(TestResult.SUCCESS)).count();
		final long unknown =
				specificResults.stream().filter(a -> a.getValue().getResult().equals(TestResult.UNKNOWN)).count();
		final long fail =
				specificResults.stream().filter(a -> a.getValue().getResult().equals(TestResult.FAIL)).count();

		sb.append(toolchainAndSettings.Toolchain.getName());
		sb.append(indent);
		sb.append(toolchainAndSettings.Setting.getName());
		sb.append(indent);
		sb.append(success);
		sb.append(indent);
		sb.append(unknown);
		sb.append(indent);
		sb.append(fail);
		sb.append(CoreUtil.getPlatformLineSeparator());
	}

}
