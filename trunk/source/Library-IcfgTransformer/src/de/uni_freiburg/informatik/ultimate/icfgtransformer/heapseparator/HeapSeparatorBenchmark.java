package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.statistics.BenchmarkWithCounters;

public class HeapSeparatorBenchmark extends BenchmarkWithCounters {
	//implements ICsvProviderProvider<Number> {

//	private int mTransformulaCounter;
//	private int mArrayUpdateCounter;
//	private int mNewlyIntroducedArrayUpdateCounter;
//	private int mNoArrayGroups;
//	private int mNoArrays;
//	private int mNoEquivalenceClasses;

//	final private List<String> mColumnTitles = new ArrayList<>();
//	final private List<Number> mResults = new ArrayList<>();

//	private boolean mAlreadyGeneratedColumnTitlesAndResults;

	private final Set<ArrayGroup> mHeapArrayGroups = new HashSet<>();

	private final NestedMap3<ArrayGroup, Integer, HeapSeparatorStatistics, Number> mPerArrayAndDimensionInfo =
			new NestedMap3<>();

	private final NestedMap2<ArrayGroup, HeapSeparatorStatistics, Number> mPerArrayInfo = new NestedMap2<>();


//	@Override
//	public ICsvProvider<Number> createCsvProvider() {
//
////		final List<String> columnTitles = new ArrayList<>();
////		final List<Integer> results = new ArrayList<>();
//
//		generateColumnTitlesAndResults();
//
////		final ICsvProvider<Number> result = new SimpleCsvProvider<>(mColumnTitles);
////		result.addRow(mResults);
//
//		return result;
//	}

	@Override
	protected void generateColumnTitlesAndResults() {
		if (mAlreadyGeneratedColumnTitlesAndResults) {
			return;
		}

		super.generateColumnTitlesAndResults();

		for (final ArrayGroup heapArrayGroup : mHeapArrayGroups) {
			for (int dim = 0; dim < heapArrayGroup.getDimensionality(); dim++) {
				for (final HeapSeparatorStatistics v : HeapSeparatorStatistics.values()) {
					// TODO group enum members..
					if (v == HeapSeparatorStatistics.COUNT_BLOCKS || v == HeapSeparatorStatistics.COUNT_ARRAY_WRITES) {
						mColumnTitles.add(v.name() + "_for_" + heapArrayGroup + "_at_dim_" + dim);
						//					mColumnTitles.add(String.format("%40s for %15 at %4s", v.name(), heapArrayGroup, "t"));
						//					mColumnTitles.add(String.format("%40s for %15s at %d", v.name(), heapArrayGroup,
						//							Integer.valueOf(dim)));
						//							Integer.toString(dim)));
						mResults.add(mPerArrayAndDimensionInfo.get(heapArrayGroup, dim, v));
					}
				}
			}
		}

		for (final ArrayGroup heapArrayGroup : mHeapArrayGroups) {
			for (final HeapSeparatorStatistics v : HeapSeparatorStatistics.values()) {
				if (v == HeapSeparatorStatistics.COUNT_ARRAY_READS) {
					mColumnTitles.add(v.name() + " for " + heapArrayGroup);
					mResults.add(mPerArrayInfo.get(heapArrayGroup, v));
				}
			}
		}

//		mAlreadyGeneratedColumnTitlesAndResults = true; // done by super

	}

	void registerArrayGroup(final ArrayGroup ag) {
		final boolean newlyAdded = mHeapArrayGroups.add(ag);
		if (newlyAdded) {
			registerCounter(getNewArrayVarCounterName(ag));
		}
	}

	private String getNewArrayVarCounterName(final ArrayGroup ag) {
		return HeapSeparatorStatistics.COUNT_NEW_ARRAY_VARS.name() + "_" + ag;
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

	public void incrementNewArrayVarCounter(final ArrayGroup arrayGroup) {
		super.incrementCounter(getNewArrayVarCounterName(arrayGroup));
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
