package de.uni_freiburg.informatik.ultimatetest.evals;

import java.io.File;
import java.util.Collection;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;

public abstract class LatexSummary extends BaseCsvProviderSummary {

	public LatexSummary(Class<? extends UltimateTestSuite> ultimateTestSuite,
			Collection<Class<? extends ICsvProviderProvider<? extends Object>>> benchmarks,
			ColumnDefinition[] columnDefinitions) {
		super(ultimateTestSuite, benchmarks, columnDefinitions);
	}

	protected Set<String> getDistinctFolderSuffixes(PartitionedResults results) {
		Set<File> folders = CoreUtil.selectDistinct(results.All, new IMyReduce<File>() {
			@Override
			public File reduce(Entry<UltimateRunDefinition, ExtendedResult> entry) {
				return entry.getKey().getInput().getParentFile();
			}
		});
	
		HashSet<String[]> working = new HashSet<>();
	
		for (File folder : folders) {
			working.add(folder.getAbsolutePath().split(Pattern.quote(File.separator)));
		}
		int offset = 0;
		boolean offsetsEqual = false;
		while (!offsetsEqual) {
			offsetsEqual = true;
			String last = null;
			for (String[] pathSegments : working) {
				String currentlast = File.separator;
				int end = pathSegments.length - 1;
				int j = end - offset;
	
				while (j <= end) {
					currentlast += pathSegments[j] + File.separator;
					++j;
				}
	
				if (!currentlast.equals(last)) {
					last = currentlast;
				} else {
					offset++;
					offsetsEqual = false;
					break;
				}
			}
		}
	
		HashSet<String> rtr = new HashSet<>();
		for (String[] pathSegments : working) {
			String suffix = "";
			for (int i = pathSegments.length - 1 - offset; i < pathSegments.length; ++i) {
				suffix += pathSegments[i] + File.separator;
			}
			suffix = suffix.substring(0, suffix.length() - File.separator.length());
			rtr.add(suffix);
		}
		assert rtr.size() == folders.size();
	
		return rtr;
	}
	
	protected boolean isInvalidForLatex(String cell) {
		return cell == null || cell.contains("[");
	}

	protected String removeInvalidCharsForLatex(String cell) {
		return cell.replace("\\", " \\textbackslash ").replace("_", "\\_");
	}

}