package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class CodeCheckBenchmarks implements ICsvProviderProvider<Object> {

	private SimpleCsvProvider<Object> mCsvP;

	@Override
	public ICsvProvider<Object> createCvsProvider() {
		if (mCsvP == null) {
			ArrayList<String> columnTitles = new ArrayList<>();
			columnTitles.add("time (ms)");
			columnTitles.add("#iterations");
			columnTitles.add(CodeCheckObserver.s_NumberOfCodeBlocks);
			columnTitles.add(CodeCheckObserver.s_SizeOfPredicates);
			columnTitles.add(CodeCheckObserver.s_ConjunctsInSSA);
			columnTitles.add(CodeCheckObserver.s_ConjunctsInUnsatCore);
			columnTitles.add("InterPolantCoveringCapability");
			mCsvP = new SimpleCsvProvider<Object>(columnTitles);
		}
		return mCsvP;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("CodeCheck benchmark data:\n");
		sb.append(mCsvP.getColumnTitles() + "\n");
		for (List<Object> l : mCsvP.getTable()) {
			for (Object i : l) {
				sb.append(i);
				sb.append("\t");
			}
			sb.append("\n");
		}
		return sb.toString();
//		return "---- bmdata -----\n" + mCsvP.getTable().toString();
	}
}
