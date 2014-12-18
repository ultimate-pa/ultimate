package de.uni_freiburg.informatik.ultimatetest.evals;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summary.NewTestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class ComparativeSummary extends NewTestSummary {

	public ComparativeSummary(Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
	}

	@Override
	public String getSummaryLog() {
		PartitionedResults partitionedResults = getAllResultsPartitioned();

		final HashMap<String, HashSet<Entry<UltimateRunDefinition, ExtendedResult>>> tool2entry = new HashMap<>();
		final HashMap<String, HashSet<String>> file2tool = new HashMap<>();
		HashMap<String, HashSet<Entry<UltimateRunDefinition, ExtendedResult>>> file2entries = new HashMap<>();

		for (Entry<UltimateRunDefinition, ExtendedResult> entry : partitionedResults.All) {
			String tool = entry.getKey().getToolchain().getAbsolutePath() + "+"
					+ entry.getKey().getSettings().getAbsolutePath();
			String filename = entry.getKey().getInput().getAbsolutePath();
			HashSet<Entry<UltimateRunDefinition, ExtendedResult>> entries = tool2entry.get(tool);
			if (entries == null) {
				entries = new HashSet<>();
				tool2entry.put(tool, entries);
			}
			entries.add(entry);

			HashSet<String> tools = file2tool.get(entry);
			if (tools == null) {
				tools = new HashSet<>();
				file2tool.put(filename, tools);
			}
			tools.add(tool);

			HashSet<Entry<UltimateRunDefinition, ExtendedResult>> fEntries = file2entries.get(filename);
			if (fEntries == null) {
				fEntries = new HashSet<>();
				file2entries.put(filename, fEntries);
			}
			fEntries.add(entry);
		}

		Collection<Entry<UltimateRunDefinition, ExtendedResult>> mismatches = CoreUtil.where(partitionedResults.Error,
				new ITestSummaryResultPredicate() {
					@Override
					public boolean check(Entry<UltimateRunDefinition, ExtendedResult> entry) {
						HashSet<String> tools = file2tool.get(entry.getKey().getInput().getAbsolutePath());
						for (String tool : tools) {
							if (!tool2entry.containsKey(tool)) {
								return false;
							}
						}
						return true;
					}
				});

		// HashSet<Entry<UltimateRunDefinition, ExtendedResult>> mismatchesSet =
		// new HashSet<>(mismatches);

		StringBuilder sb = new StringBuilder();
		sb.append("#################");
		sb.append(" Mismatching errors ");
		sb.append("#################");
		sb.append(CoreUtil.getPlatformLineSeparator());
		String indent = "    ";
		for (Entry<UltimateRunDefinition, ExtendedResult> mismatch : mismatches) {
			String filename = mismatch.getKey().getInput().getAbsolutePath();
			sb.append(Util.removeTrunkExamplesPrefix(filename));
			sb.append(CoreUtil.getPlatformLineSeparator());
			for (Entry<UltimateRunDefinition, ExtendedResult> differentEntry : file2entries.get(filename)) {
				String tool = Util.removeTrunkToolchainPrefix(differentEntry.getKey().getToolchain().getAbsolutePath())
						+ "+" + Util.removeTrunkSettingsPrefix(differentEntry.getKey().getSettings().getAbsolutePath());
				sb.append(indent);
				sb.append(tool);
				sb.append(CoreUtil.getPlatformLineSeparator());
				sb.append(indent).append(indent);
				sb.append(differentEntry.getValue().Message);
				sb.append(CoreUtil.getPlatformLineSeparator());
			}
			sb.append(CoreUtil.getPlatformLineSeparator());
		}
		return sb.toString();
	}

}
