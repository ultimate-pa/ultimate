/*
 * Copyright (C) 2019 Julian Löffler (loefflju@informatik.uni-freiburg.de), Breee@github
 * Copyright (C) 2012-2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Path;
import java.time.ZonedDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class SMTFeatureExtractor {

	private final ILogger mLogger;
	private final List<SMTFeature> mFeatures;
	private final Path mDumpPath;
	private final Path mFilename;
	private final boolean mDumpFeatures;

	public SMTFeatureExtractor(final ILogger logger, final String dump_path, final boolean dump_features) {
		mLogger = logger;
		mFeatures = new ArrayList<>();
		mDumpFeatures = dump_features;
		if (dump_features) {
			mDumpPath = new File(dump_path).toPath();
			final String timestamp = ZonedDateTime.now().format(DateTimeFormatter.ofPattern("uuuu-MM-dd"));
			mFilename = mDumpPath.resolve(timestamp + "-smtfeatures.csv");
			createDumpFile();
		} else {
			mDumpPath = null;
			mFilename = null;
		}
	}

	public SMTFeature extractFeatureRaw(final Term term) {
		final SMTFeatureExtractionTermClassifier tc = new SMTFeatureExtractionTermClassifier();
		tc.checkTerm(term);
		final SMTFeature feature = new SMTFeature();
		feature.containsArrays = tc.hasArrays();
		feature.occuringFunctions = tc.getOccuringFunctionNames();
		feature.occuringQuantifiers = tc.getOccuringQuantifiers();
		feature.occuringSorts = tc.getOccuringSortNames();
		feature.numberOfFunctions = tc.getNumberOfFunctions();
		feature.numberOfQuantifiers = tc.getNumberOfQuantifiers();
		feature.numberOfVariables = tc.getNumberOfVariables();
		feature.numberOfArrays = tc.getNumberOfArrays();
		feature.numberOfSelectFunctions = tc.getOccuringFunctionNames().getOrDefault("select", 0);
		feature.numberOfStoreFunctions = tc.getOccuringFunctionNames().getOrDefault("store", 0);
		feature.dagsize = tc.getDAGSize();
		feature.dependencyScore = tc.getDependencyScore();
		feature.variableEquivalenceClassSizes = tc.getVariableEquivalenceClassSizes();
		feature.biggestEquivalenceClass = tc.getBiggestEquivalenceClass();
		return feature;
	}

	public void extractFeature(final List<Term> assertions, final double time, final String result,
			final String solvername) throws IllegalAccessException, IOException {
		final SMTFeatureExtractionTermClassifier tc = new SMTFeatureExtractionTermClassifier();
		for (final Term term : assertions) {
			tc.checkTerm(term);
		}
		final SMTFeature feature = new SMTFeature();
		// feature.assertionStack = tc.getAssertionStack();
		feature.assertionStackHashCode = tc.getAssertionStack().hashCode();
		feature.containsArrays = tc.hasArrays();
		feature.occuringFunctions = tc.getOccuringFunctionNames();
		feature.occuringQuantifiers = tc.getOccuringQuantifiers();
		feature.occuringSorts = tc.getOccuringSortNames();
		feature.numberOfFunctions = tc.getNumberOfFunctions();
		feature.numberOfQuantifiers = tc.getNumberOfQuantifiers();
		feature.numberOfVariables = tc.getNumberOfVariables();
		feature.numberOfArrays = tc.getNumberOfArrays();
		feature.dagsize = tc.getDAGSize();
		feature.treesize = tc.getTreeSize();
		feature.dependencyScore = tc.getDependencyScore();
		feature.variableEquivalenceClassSizes = tc.getVariableEquivalenceClassSizes();
		feature.biggestEquivalenceClass = tc.getBiggestEquivalenceClass();
		feature.solverresult = result;
		feature.solvertime = time;
		feature.solvername = solvername;
		mFeatures.add(feature);
		if (mDumpFeatures) {
			dumpFeature(feature);
		}
	}

	public void dumpFeature(final SMTFeature feature) throws IllegalAccessException, IOException {

		try (FileWriter fw = new FileWriter(mFilename.toString(), true);
				BufferedWriter bw = new BufferedWriter(fw);
				PrintWriter out = new PrintWriter(bw)) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("################## SMT DUMP #####################");
				mLogger.debug("Writing to file:" + mFilename);
				mLogger.debug(SMTFeature.getCsvHeader(";"));
				mLogger.debug("FEATURE: " + feature);
				mLogger.debug("#################################################");
			}
			out.println(feature.toCsv(";"));
		} catch (final IOException e) {
			throw new IOException(e);
		}
	}

	private void createDumpFile() {
		final File f = new File(mFilename.toString());
		if (!f.exists()) {
			try {
				f.createNewFile();
				try (FileWriter fw = new FileWriter(mFilename.toString(), true);
						BufferedWriter bw = new BufferedWriter(fw);
						PrintWriter out = new PrintWriter(bw)) {
					final String header = SMTFeature.getCsvHeader(";");
					out.println(header);
				} catch (IOException | IllegalAccessException e) {
					mLogger.error(e);
				}

			} catch (final IOException e) {
				mLogger.error(e);
			}
		}
	}

}
