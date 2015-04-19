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
 * List which toolchain/setting pair combinations were able to solve which files.
 * 
 * @author Matthias Heizmann
 *
 */
public class WhoSolvedItSummary extends NewTestSummary {

	public WhoSolvedItSummary(
			Class<? extends UltimateTestSuite> ultimateTestSuite) {
		super(ultimateTestSuite);
	}
	
	@Override
	public String getSummaryLog() {
		PartitionedResults pr = getAllResultsPartitioned();
		Collection<Entry<UltimateRunDefinition, ExtendedResult>> test = pr.Success;
		
		HashRelation<File, TCS> input2tcses = new HashRelation<>();
		for (Entry<UltimateRunDefinition, ExtendedResult> result : test) {
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
		StringBuilder sb = new StringBuilder();
		Arrays.sort(tcsPowerset, comp);
		for (Set<TCS> tcses : tcsPowerset) {
			sb.append("The " + tcses.size() + " toolchain/settings pairs").append(System.lineSeparator());
			for (TCS tcs : tcses) {
				sb.append("    ").append(tcs).append(System.lineSeparator());
			}
			Set<File> inputFiles = tcses2input.getImage(tcses);
			sb.append("are exactly the pairs that were successfull on the following " + inputFiles.size() + " files").append(System.lineSeparator());
			for (File file : inputFiles) {
				sb.append("  ").append(file.getAbsolutePath()).append(System.lineSeparator());
			}
			sb.append(System.lineSeparator());
		}
		return sb.toString();
	}

}
