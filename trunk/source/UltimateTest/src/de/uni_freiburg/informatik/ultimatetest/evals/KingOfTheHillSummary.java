package de.uni_freiburg.informatik.ultimatetest.evals;

import java.io.File;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summary.NewTestSummary;

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
		
		HashRelation<File, TCS> input2tcses = new HashRelation<>();
		for (Entry<UltimateRunDefinition, ExtendedResult> result : allOfResultCategory) {
			UltimateRunDefinition urd = result.getKey();
			TCS tcs = new TCS(urd.getToolchain(), urd.getSettings());
			input2tcses.addPair(urd.getInput(), tcs);
		}
		HashRelation<Set<TCS>, File> tcses2input = new HashRelation<>();
		for (File input : input2tcses.getDomain()) {
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
			Set<File> inputFiles = tcses2input.getImage(tcses);
			sb.append("are exactly the pairs were the result was "); 
			sb.append(resultCategory);
			sb.append(" on the following ");
			sb.append(inputFiles.size());
			sb.append(" files").append(System.lineSeparator());
			for (File file : inputFiles) {
				sb.append("  ").append(file.getAbsolutePath()).append(System.lineSeparator());
			}
			sb.append(System.lineSeparator());
		}
	}

}
