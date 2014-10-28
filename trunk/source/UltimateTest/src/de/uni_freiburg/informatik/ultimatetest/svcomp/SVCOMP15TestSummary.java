package de.uni_freiburg.informatik.ultimatetest.svcomp;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider.TestResult;
import de.uni_freiburg.informatik.ultimatetest.summary.NewTestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * This summary should only be used with {@link SVCOMP15TestSuite}, because it
 * relies on the name of the test case generated there to extract the SVCOMP
 * category of a given test.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class SVCOMP15TestSummary extends NewTestSummary {

	public SVCOMP15TestSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
	}

	@Override
	public String getSummaryLog() {

		Set<TCS> tcs = de.uni_freiburg.informatik.ultimate.core.util.Util.selectDistinct(mResults.entrySet(), new IMyReduce<TCS>() {
			@Override
			public TCS reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return new TCS(entry.getKey().getToolchain(), entry.getKey().getSettings());
			}
		});

		Set<String> svcompCategories = de.uni_freiburg.informatik.ultimate.core.util.Util.selectDistinct(mResults.entrySet(), new IMyReduce<String>() {
			@Override
			public String reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getValue().Testname.split(" ")[0];
			}
		});

		StringBuilder sb = new StringBuilder();
		String indent = "\t";
		for (final TCS atcs : tcs) {
			for (final String svcompCategory : svcompCategories) {
				Collection<Entry<UltimateRunDefinition, ExtendedResult>> results = de.uni_freiburg.informatik.ultimate.core.util.Util.where(mResults.entrySet(),
						new ITestSummaryResultPredicate() {
							@Override
							public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
								return entry.getKey().getToolchain().equals(atcs.Toolchain)
										&& entry.getKey().getSettings().equals(atcs.Setting)
										&& entry.getValue().Testname.split(" ")[0].equals(svcompCategory);
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
				sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());

				StringBuilder summary = new StringBuilder();
				int totalCount = 0;
				// write the result type and the content (SUCCESS, UNKNOWN,
				// FAIL)
				for (final TestResult tResult : TestResult.values()) {
					Collection<Entry<UltimateRunDefinition, ExtendedResult>> specificResults = de.uni_freiburg.informatik.ultimate.core.util.Util.where(results,
							new ITestSummaryResultPredicate() {
								@Override
								public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
									return entry.getValue().Result == tResult;
								}
							});

					summary.append(tResult).append(": ").append(specificResults.size())
							.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());

					if (specificResults.isEmpty()) {
						continue;
					}
					totalCount += specificResults.size();

					sb.append("===== ");
					sb.append(tResult);
					sb.append(" =====").append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());

					Set<String> resultCategories = de.uni_freiburg.informatik.ultimate.core.util.Util.selectDistinct(specificResults, new IMyReduce<String>() {
						@Override
						public String reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
							return entry.getValue().Category;
						}
					});

					for (final String resultCategory : resultCategories) {
						// group by result category
						sb.append(indent).append(resultCategory).append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
						Collection<Entry<UltimateRunDefinition, ExtendedResult>> resultsByCategory = de.uni_freiburg.informatik.ultimate.core.util.Util.where(
								results, new ITestSummaryResultPredicate() {
									@Override
									public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
										return entry.getValue().Category.equals(resultCategory);
									}
								});
						for (Entry<UltimateRunDefinition, ExtendedResult> entry : resultsByCategory) {

							// name of the file
							sb.append(indent).append(indent);
							sb.append(entry.getKey().getInput().getParentFile().getName());
							sb.append(File.separator);
							sb.append(entry.getKey().getInput().getName());
							sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());

							// message
							sb.append(indent).append(indent).append(indent).append(entry.getValue().Message)
									.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());

						}

						sb.append(indent).append("Total: ").append(resultsByCategory.size())
								.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
						sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
					}
					sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
				}

				sb.append("===== TOTAL =====").append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
				sb.append(summary.toString());
				sb.append("All: ").append(totalCount).append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
				sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
			}

		}

		HashMap<String, Integer> nemesisMap = new HashMap<>();
		for (Entry<UltimateRunDefinition, ExtendedResult> entry : mResults.entrySet()) {
			if (entry.getValue().Result.equals(TestResult.SUCCESS)) {
				continue;
			}

			String message = entry.getValue().Message.intern();
			if (!nemesisMap.containsKey(message)) {
				nemesisMap.put(message, 1);
			} else {
				nemesisMap.put(message, nemesisMap.get(message) + 1);
			}
		}

		List<Entry<String, Integer>> nemesis = new ArrayList<>(nemesisMap.entrySet());
		Collections.sort(nemesis, new Comparator<Entry<String, Integer>>() {
			@Override
			public int compare(Entry<String, Integer> o1, Entry<String, Integer> o2) {
				return -o1.getValue().compareTo(o2.getValue());
			}
		});

		sb.append("################# Reasons for !SUCCESS #################").append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
		for (Entry<String, Integer> entry : nemesis) {
			sb.append(entry.getValue()).append(indent).append(entry.getKey()).append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
		}
		sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());

		sb.append("################# Total Comparison #################").append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
		sb.append("Toolchain").append(indent);
		sb.append("Settings").append(indent);
		sb.append("Success").append(indent);
		sb.append("Unknown").append(indent);
		sb.append("Fail").append(indent);
		sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
		for (final TCS toolchainAndSettings : tcs) {
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> specificResults = de.uni_freiburg.informatik.ultimate.core.util.Util.where(mResults.entrySet(),
					new ITestSummaryResultPredicate() {
						@Override
						public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
							return entry.getKey().getToolchain().equals(toolchainAndSettings.Toolchain)
									&& entry.getKey().getSettings().equals(toolchainAndSettings.Setting);
						}
					});
			appendComparison(sb, indent, toolchainAndSettings, specificResults);
		}

		sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
		sb.append("################# Comparison by SVCOMP Category #################").append(
				de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());

		sb.append("SVCOMP-Cat.").append(indent);
		sb.append("Toolchain").append(indent);
		sb.append("Settings").append(indent);
		sb.append("Success").append(indent);
		sb.append("Unknown").append(indent);
		sb.append("Fail").append(indent);
		sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
		for (final TCS toolchainAndSettings : tcs) {
			for (final String svcompCategory : svcompCategories) {
				Collection<Entry<UltimateRunDefinition, ExtendedResult>> specificResults = de.uni_freiburg.informatik.ultimate.core.util.Util.where(
						mResults.entrySet(), new ITestSummaryResultPredicate() {
							@Override
							public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
								return entry.getKey().getToolchain().equals(toolchainAndSettings.Toolchain)
										&& entry.getKey().getSettings().equals(toolchainAndSettings.Setting)
										&& entry.getValue().Testname.split(" ")[0].equals(svcompCategory);
							}
						});
				sb.append(svcompCategory).append(indent);
				appendComparison(sb, indent, toolchainAndSettings, specificResults);
			}

		}

		return sb.toString();
	}

	private void appendComparison(StringBuilder sb, String indent, final TCS toolchainAndSettings,
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> specificResults) {

		int success = de.uni_freiburg.informatik.ultimate.core.util.Util.where(specificResults, new ITestSummaryResultPredicate() {
			@Override
			public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getValue().Result.equals(TestResult.SUCCESS);
			}
		}).size();

		int unknown = de.uni_freiburg.informatik.ultimate.core.util.Util.where(specificResults, new ITestSummaryResultPredicate() {
			@Override
			public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getValue().Result.equals(TestResult.UNKNOWN);
			}
		}).size();

		int fail = de.uni_freiburg.informatik.ultimate.core.util.Util.where(specificResults, new ITestSummaryResultPredicate() {
			@Override
			public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getValue().Result.equals(TestResult.FAIL);
			}
		}).size();

		sb.append(toolchainAndSettings.Toolchain.getName());
		sb.append(indent);
		sb.append(toolchainAndSettings.Setting.getName());
		sb.append(indent);
		sb.append(success);
		sb.append(indent);
		sb.append(unknown);
		sb.append(indent);
		sb.append(fail);
		sb.append(de.uni_freiburg.informatik.ultimate.core.util.Util.getPlatformLineSeparator());
	}

}
