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

	final private List<String> mColumnTitles = new ArrayList<>();
	final private List<Integer> mResults = new ArrayList<>();
	private boolean mAlreadyGeneratedColumnTitlesAndResults;

	@Override
	public ICsvProvider<Integer> createCsvProvider() {

//		final List<String> columnTitles = new ArrayList<>();
//		final List<Integer> results = new ArrayList<>();

		generateColumnTitlesAndResults();

		final ICsvProvider<Integer> result = new SimpleCsvProvider<>(mColumnTitles);
		result.addRow(mResults);

		return result;
	}

	protected void generateColumnTitlesAndResults() {
		if (mAlreadyGeneratedColumnTitlesAndResults) {
			return;
		}
		mColumnTitles.add("#Transformulas");
		mResults.add(mTransformulaCounter);

		mColumnTitles.add("#ArrayUpdatesInInput");
		mResults.add(mArrayUpdateCounter);

		mColumnTitles.add("#ArrayUpdatesInResult");
		mResults.add(mNewlyIntroducedArrayUpdateCounter);

		mColumnTitles.add("#ArraysInInput");
		mResults.add(mNoArrays);

		mColumnTitles.add("#ArrayGroups");
		mResults.add(mNoArrayGroups);

		mColumnTitles.add("#EquivalenceClasses");
		mResults.add(mNoEquivalenceClasses);

		mAlreadyGeneratedColumnTitlesAndResults = true;

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
		generateColumnTitlesAndResults();

		final StringBuilder sb = new StringBuilder();

		sb.append("\n");

		for (int i = 0; i < mColumnTitles.size(); i++) {
			sb.append(String.format("%-40s : %7d %n", mColumnTitles.get(i), mResults.get(i)));
		}
		return sb.toString();
	}

	/**
	 * Arrays are in one group if they are equated somewhere in the program.
	 * @param size
	 */
	public void setNoArrayGroups(final int size) {
		mNoArrayGroups = size;
	}

	public void setNoArrays(final int size) {
		mNoArrays = size;
	}

	/**
	 * the number of overall equivalence classes (when this is equal to NoArrayGroups, no split has taken place)
	 */
	public void incrementEquivalenceClassCounter() {
		mNoEquivalenceClasses++;
	}
}
