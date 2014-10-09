package de.uni_freiburg.informatik.ultimatetest.svcomp;

import java.io.File;
import java.util.Collection;
import java.util.Set;
import java.util.Map.Entry;

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

		Set<TCS> tcs = getDistinct(mResults.entrySet(), new IReduce<TCS>() {
			@Override
			public TCS reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return new TCS(entry.getKey().getToolchain(), entry.getKey().getSettings());
			}
		});

		Set<String> svcompCategories = getDistinct(mResults.entrySet(), new IReduce<String>() {
			@Override
			public String reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getValue().Testname.split(" ")[0];
			}
		});

		StringBuilder sb = new StringBuilder();
		String indent = "\t";
		for (final TCS atcs : tcs) {
			for (final String svcompCategory : svcompCategories) {
				Collection<Entry<UltimateRunDefinition, ExtendedResult>> results = getResultsWhere(mResults.entrySet(),
						new IPredicate() {
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
				sb.append(Util.getPlatformLineSeparator());

				StringBuilder summary = new StringBuilder();
				int totalCount = 0;
				// write the result type and the content (SUCCESS, UNKNOWN,
				// FAIL)
				for (final TestResult tResult : TestResult.values()) {
					Collection<Entry<UltimateRunDefinition, ExtendedResult>> specificResults = getResultsWhere(results,
							new IPredicate() {
								@Override
								public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
									return entry.getValue().Result == tResult;
								}
							});

					summary.append(tResult).append(": ").append(specificResults.size())
							.append(Util.getPlatformLineSeparator());

					if (specificResults.isEmpty()) {
						continue;
					}
					totalCount += specificResults.size();

					sb.append("===== ");
					sb.append(tResult);
					sb.append(" =====").append(Util.getPlatformLineSeparator());

					Set<String> resultCategories = getDistinct(specificResults, new IReduce<String>() {
						@Override
						public String reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
							return entry.getValue().Category;
						}
					});

					for (final String resultCategory : resultCategories) {
						// group by result category
						sb.append(indent).append(resultCategory).append(Util.getPlatformLineSeparator());
						Collection<Entry<UltimateRunDefinition, ExtendedResult>> resultsByCategory = getResultsWhere(
								results, new IPredicate() {
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
							sb.append(Util.getPlatformLineSeparator());

							// message
							sb.append(indent).append(indent).append(indent).append(entry.getValue().Message)
									.append(Util.getPlatformLineSeparator());

						}
					}
					sb.append(Util.getPlatformLineSeparator());
				}

				sb.append("===== TOTAL =====").append(Util.getPlatformLineSeparator());
				sb.append(summary.toString());
				sb.append("All: ").append(totalCount).append(Util.getPlatformLineSeparator());
				sb.append(Util.getPlatformLineSeparator());
			}

		}

		sb.append("################# Total Comparison #################").append(Util.getPlatformLineSeparator());
		sb.append("Toolchain").append(indent);
		sb.append("Settings").append(indent);
		sb.append("Success").append(indent);
		sb.append("Unknown").append(indent);
		sb.append("Fail").append(indent);
		sb.append(Util.getPlatformLineSeparator());
		for (final TCS toolchainAndSettings : tcs) {
			Collection<Entry<UltimateRunDefinition, ExtendedResult>> specificResults = getResultsWhere(
					mResults.entrySet(), new IPredicate() {
						@Override
						public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
							return entry.getKey().getToolchain().equals(toolchainAndSettings.Toolchain)
									&& entry.getKey().getSettings().equals(toolchainAndSettings.Setting);
						}
					});
			appendComparison(sb, indent, toolchainAndSettings, specificResults);
		}

		sb.append(Util.getPlatformLineSeparator());
		sb.append("################# Comparison by SVCOMP Category #################").append(
				Util.getPlatformLineSeparator());

		sb.append("SVCOMP-Cat.").append(indent);
		sb.append("Toolchain").append(indent);
		sb.append("Settings").append(indent);
		sb.append("Success").append(indent);
		sb.append("Unknown").append(indent);
		sb.append("Fail").append(indent);
		sb.append(Util.getPlatformLineSeparator());
		for (final TCS toolchainAndSettings : tcs) {
			for (final String svcompCategory : svcompCategories) {
				Collection<Entry<UltimateRunDefinition, ExtendedResult>> specificResults = getResultsWhere(
						mResults.entrySet(), new IPredicate() {
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

		int success = getResultsWhere(specificResults, new IPredicate() {
			@Override
			public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getValue().Result.equals(TestResult.SUCCESS);
			}
		}).size();

		int unknown = getResultsWhere(specificResults, new IPredicate() {
			@Override
			public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getValue().Result.equals(TestResult.UNKNOWN);
			}
		}).size();

		int fail = getResultsWhere(specificResults, new IPredicate() {
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
		sb.append(Util.getPlatformLineSeparator());
	}
}
