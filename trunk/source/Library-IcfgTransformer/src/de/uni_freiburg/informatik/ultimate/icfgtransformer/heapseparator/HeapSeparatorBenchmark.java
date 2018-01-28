package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

public class HeapSeparatorBenchmark implements ICsvProviderProvider<Number> {

//	private int mTransformulaCounter;
//	private int mArrayUpdateCounter;
//	private int mNewlyIntroducedArrayUpdateCounter;
//	private int mNoArrayGroups;
//	private int mNoArrays;
//	private int mNoEquivalenceClasses;

	final private List<String> mColumnTitles = new ArrayList<>();
	final private List<Number> mResults = new ArrayList<>();

	private boolean mAlreadyGeneratedColumnTitlesAndResults;

	private final Set<ArrayGroup> mHeapArrayGroups = new HashSet<>();

	private final NestedMap3<ArrayGroup, Integer, HeapSeparatorStatistics, Number> mPerArrayAndDimensionInfo =
			new NestedMap3<>();

	private final NestedMap2<ArrayGroup, HeapSeparatorStatistics, Number> mPerArrayInfo = new NestedMap2<>();


	@Override
	public ICsvProvider<Number> createCsvProvider() {

//		final List<String> columnTitles = new ArrayList<>();
//		final List<Integer> results = new ArrayList<>();

		generateColumnTitlesAndResults();

		final ICsvProvider<Number> result = new SimpleCsvProvider<>(mColumnTitles);
		result.addRow(mResults);

		return result;
	}

	protected void generateColumnTitlesAndResults() {
		if (mAlreadyGeneratedColumnTitlesAndResults) {
			return;
		}
//		mColumnTitles.add("#Transformulas");
//		mResults.add(mTransformulaCounter);
//
//		mColumnTitles.add("#ArrayUpdatesInInput");
//		mResults.add(mArrayUpdateCounter);
//
//		mColumnTitles.add("#ArrayUpdatesInResult");
//		mResults.add(mNewlyIntroducedArrayUpdateCounter);
//
//		mColumnTitles.add("#ArraysInInput");
//		mResults.add(mNoArrays);
//
//		mColumnTitles.add("#ArrayGroups");
//		mResults.add(mNoArrayGroups);
//
//		mColumnTitles.add("#EquivalenceClasses");
//		mResults.add(mNoEquivalenceClasses);

		for (final ArrayGroup heapArrayGroup : mHeapArrayGroups) {
			for (int dim = 0; dim < heapArrayGroup.getDimensionality(); dim++) {
				for (final HeapSeparatorStatistics v : HeapSeparatorStatistics.values()) {
					if (v == HeapSeparatorStatistics.COUNT_ARRAY_READS) {
						// TODO group enum members..
						continue;
					}
					mColumnTitles.add(v.name() + "_for_" + heapArrayGroup + "_at_dim_" + dim);
//					mColumnTitles.add(String.format("%40s for %15 at %4s", v.name(), heapArrayGroup, "t"));
//					mColumnTitles.add(String.format("%40s for %15s at %d", v.name(), heapArrayGroup,
//							Integer.valueOf(dim)));
//							Integer.toString(dim)));
					mResults.add(mPerArrayAndDimensionInfo.get(heapArrayGroup, dim, v));
				}
			}
		}

		for (final ArrayGroup heapArrayGroup : mHeapArrayGroups) {
			for (final HeapSeparatorStatistics v : HeapSeparatorStatistics.values()) {
				if (v != HeapSeparatorStatistics.COUNT_ARRAY_READS) {
						// TODO group enum members..
						continue;
				}
				mColumnTitles.add(v.name() + " for " + heapArrayGroup);
				mResults.add(mPerArrayInfo.get(heapArrayGroup, v));

			}
		}

		mAlreadyGeneratedColumnTitlesAndResults = true;

	}

	void registerArrayGroup(final ArrayGroup ag) {
		mHeapArrayGroups.add(ag);
	}

	void registerPerArrayInfo(final ArrayGroup ag, final HeapSeparatorStatistics hss, final Number value) {
		mPerArrayInfo.put(ag, hss, value);
	}

	void registerPerArrayAndDimensionInfo(final ArrayGroup ag, final int dim, final HeapSeparatorStatistics hss,
			final Number value) {
		mPerArrayAndDimensionInfo.put(ag, dim, hss, value);

	}

//	void incrementTransformulaCounter() {
//		mTransformulaCounter++;
//	}
//
//	void incrementArrayUpdateCounter() {
//		mArrayUpdateCounter++;
//	}
//
//	void incrementNewlyIntroducedArrayUpdateCounter() {
//		mNewlyIntroducedArrayUpdateCounter++;
//	}

	@Override
	public String toString() {
		generateColumnTitlesAndResults();

		final StringBuilder sb = new StringBuilder();

		sb.append("\n");

		for (int i = 0; i < mColumnTitles.size(); i++) {
			sb.append(String.format("%-80s : %7d %n", mColumnTitles.get(i), mResults.get(i)));
		}
		return sb.toString();
	}

//	/**
//	 * Arrays are in one group if they are equated somewhere in the program.
//	 * @param size
//	 */
//	public void setNoArrayGroups(final int size) {
//		mNoArrayGroups = size;
//	}
//
//	public void setNoArrays(final int size) {
//		mNoArrays = size;
//	}
//
//	/**
//	 * the number of overall equivalence classes (when this is equal to NoArrayGroups, no split has taken place)
//	 */
//	public void incrementEquivalenceClassCounter() {
//		mNoEquivalenceClasses++;
//	}

}
