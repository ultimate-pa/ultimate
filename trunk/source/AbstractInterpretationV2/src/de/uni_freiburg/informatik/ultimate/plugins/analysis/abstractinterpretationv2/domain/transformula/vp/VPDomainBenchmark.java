package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class VPDomainBenchmark implements ICsvProviderProvider<Integer> {

	private int mSupportingEqualitiesCounter;
	private int mLocationsCounter;
	private int mSupportingDisequalitiesCounter;

	@Override
	public ICsvProvider<Integer> createCsvProvider() {
		final List<String> columnTitles = new ArrayList<>();
		final List<Integer> results = new ArrayList<>();

		columnTitles.add("#Locations");
		results.add(mLocationsCounter);

		columnTitles.add("#SupportingEqualities");
		results.add(mSupportingEqualitiesCounter);

		columnTitles.add("#SupportingDisequalities");
		results.add(mSupportingDisequalitiesCounter);

		columnTitles.add("Average#SupportingEqualities");
		results.add(mSupportingEqualitiesCounter/mLocationsCounter);

		columnTitles.add("Average#SupportingDisequalities");
		results.add(mSupportingDisequalitiesCounter/mLocationsCounter);

		final ICsvProvider<Integer> result = new SimpleCsvProvider<>(columnTitles);
		result.addRow(results);

		return result;
	}

	public void setSupportingEqualitiesCounter(final int supportingEqualitiesCounter) {
		mSupportingEqualitiesCounter = supportingEqualitiesCounter;
	}

	public void setLocationsCounter(final int locationsCounter) {
		mLocationsCounter = locationsCounter;
	}

	public void setSupportingDisequalitiesCounter(final int supportingDisequalitiesCounter) {
		mSupportingDisequalitiesCounter = supportingDisequalitiesCounter;
	}



}

