package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class HeapSeparatorBenchmark implements ICsvProviderProvider<Integer> {

	private int mTransformulaCounter;
	private int mArrayUpdateCounter;
	private int mNewlyIntroducedArrayUpdateCounter;
	private int mNoArrayGroups;
	private int mNoArrays;
	private int mNoEquivalenceClasses;

	@Override
	public ICsvProvider<Integer> createCsvProvider() {
		
		final List<String> columnTitles = new ArrayList<>();
		final List<Integer> results = new ArrayList<>();

		columnTitles.add("#Transformulas");
		results.add(mTransformulaCounter);

		columnTitles.add("#ArrayUpdatesInInput");
		results.add(mArrayUpdateCounter);

		columnTitles.add("#ArrayUpdatesInResult");
		results.add(mNewlyIntroducedArrayUpdateCounter);

		columnTitles.add("#ArraysInInput");
		results.add(mNoArrays);

		columnTitles.add("#ArrayGroups");
		results.add(mNoArrayGroups);

		columnTitles.add("#EquivalenceClasses");
		results.add(mNoEquivalenceClasses);
		
		final ICsvProvider<Integer> result = new SimpleCsvProvider<>(columnTitles);
		result.addRow(results);

		return result;
	}
	
	void incrementTransformulaCounter() {
		mTransformulaCounter++;
	}

	void incrementArrayUpdateCounter() {
		mArrayUpdateCounter++;
	}

	void incrementNewlyIntroducedArrayUpdateCounter() {
		mNewlyIntroducedArrayUpdateCounter++;
	}

	@Override
	public String toString() {
		return createCsvProvider().toString();
	}

	/**
	 * Arrays are in one group if they are equated somewhere in the program.
	 * @param size
	 */
	public void setNoArrayGroups(int size) {
		mNoArrayGroups = size;
	}

	public void setNoArrays(int size) {
		mNoArrays = size;
	}

	/**
	 * the number of overall equivalence classes (when this is equal to NoArrayGroups, no split has taken place)
	 */
	public void incrementEquivalenceClassCounter() {
		mNoEquivalenceClasses++;
	}
}
