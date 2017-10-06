/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
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


	private boolean alreadyGeneratedColumnTitlesAndResults = false;
	final private List<String> mColumnTitles = new ArrayList<>();
	final private List<Integer> mResults = new ArrayList<>();

	@Override
	public ICsvProvider<Integer> createCsvProvider() {
		generateColumnTitlesAndResults();

		final ICsvProvider<Integer> result = new SimpleCsvProvider<>(mColumnTitles);
		result.addRow(mResults);

		return result;
	}

	protected void generateColumnTitlesAndResults() {
		if (alreadyGeneratedColumnTitlesAndResults) {
			return;
		}

		mColumnTitles.add("#Locations");
		mResults.add(mLocationsCounter);

		mColumnTitles.add("#SupportingEqualities");
		mResults.add(mSupportingEqualitiesCounter);

		mColumnTitles.add("#SupportingDisequalities");
		mResults.add(mSupportingDisequalitiesCounter);

		mColumnTitles.add("Average#SupportingEqualities");
		mResults.add(mSupportingEqualitiesCounter/mLocationsCounter);

		mColumnTitles.add("Average#SupportingDisequalities");
		mResults.add(mSupportingDisequalitiesCounter/mLocationsCounter);

		assert mColumnTitles.size() == mResults.size();
		alreadyGeneratedColumnTitlesAndResults = true;
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

	@Override
	public String toString() {
		generateColumnTitlesAndResults();

		final StringBuilder sb = new StringBuilder();

		sb.append("\n");

		for (int i = 0; i < mColumnTitles.size(); i++) {
			sb.append(String.format("%-40s : %7d %n", mColumnTitles.get(i), mResults.get(i)));
//			sb.append("\t");
//			sb.append(mColumnTitles.get(i));
//			sb.append(":\t\t");
//			sb.append(mResults.get(i));
//			sb.append("\n");
		}
		return sb.toString();
	}
}

