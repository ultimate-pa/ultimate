package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class CodeCheckBenchmarks implements ICsvProviderProvider<Integer> {

	private SimpleCsvProvider<Integer> mCsvP;

	@Override
	public ICsvProvider<Integer> createCvsProvider() {
		ArrayList<String> columnTitles = new ArrayList<>();
		columnTitles.add("time (ms)");
		columnTitles.add("#iterations");
		mCsvP = new SimpleCsvProvider<Integer>(columnTitles);
		return mCsvP;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("CodeCheck benchmark data:\n");
		sb.append(mCsvP.getColumnTitles() + "\n");
		for (List<Integer> l : mCsvP.getTable()) {
			for (Integer i : l) {
				sb.append(i);
				sb.append("\t");
			}
			sb.append("\n");
		}
		return sb.toString();
//		return "---- bmdata -----\n" + mCsvP.getTable().toString();
	}
}
