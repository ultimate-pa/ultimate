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

package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.time.ZonedDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class SMTFeatureExtractor {

	private final ILogger mLogger;
	private final List<SMTFeature> mFeatures;
	private final String mDumpPath;
	private final String mFilename;

	public SMTFeatureExtractor(final ILogger logger, final String dump_path) {
		mLogger = logger;
		mFeatures = new ArrayList<>();
		mDumpPath = dump_path;
		final String timestamp = ZonedDateTime.now().format(DateTimeFormatter.ofPattern("uuuu-MM-dd"));
		mFilename = mDumpPath + timestamp + "-smtfeatures.csv";
		createDumpFile();
	}

	public void extractFeature(final List<Term> assertions, final double time, final String result)
			throws IllegalAccessException, IOException {
		mLogger.warn("Extracting feature..");
		final SMTFeatureExtractionTermClassifier tc = new SMTFeatureExtractionTermClassifier(mLogger);
		for (final Term term : assertions) {
			tc.checkTerm(term);
		}
		final SMTFeature feature = new SMTFeature();
		feature.assertionStack = tc.getAssertionStack();
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
		mFeatures.add(feature);
		dumpFeature(feature);

	}

	public void dumpFeature(final SMTFeature feature) throws IllegalAccessException, IOException {
		mLogger.info("Writing to file:" + mFilename);
		mLogger.info("FEATURE: " + feature);
		try (FileWriter fw = new FileWriter(mFilename, true);
				BufferedWriter bw = new BufferedWriter(fw);
				PrintWriter out = new PrintWriter(bw)) {
			mLogger.warn(SMTFeature.getCsvHeader(";"));
			out.println(feature.toCsv(";"));
		} catch (final IOException e) {
			throw new IOException(e);
		}
	}

	private void createDumpFile() {
		final File f = new File(mFilename);
		if (!f.exists()) {
			try {
				f.createNewFile();
				try (FileWriter fw = new FileWriter(mFilename, true);
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
		} else {
			mLogger.warn("SMT feature dump-file already exists.");
		}
	}

}
