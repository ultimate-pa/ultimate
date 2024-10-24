/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.witnessparser.preferences.WitnessParserPreferences;

/**
 * Extract the witness entries and map each location (represented by {@link IASTNode}) to the set of
 * {@link IExtractedWitnessEntry} that belong to this location.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class CorrectnessWitnessExtractor {

	private final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;
	protected IPreferenceProvider mPrefs;
	protected final boolean mIgnoreUnmatchedEntries;

	protected IASTTranslationUnit mTranslationUnit;
	private IExtractedCorrectnessWitness mResult;
	protected ExtractionStatistics mStats;

	public CorrectnessWitnessExtractor(final IUltimateServiceProvider service) {
		mServices = service;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mPrefs = WitnessParserPreferences.getPrefs(service);
		mIgnoreUnmatchedEntries = mPrefs.getBoolean(WitnessParserPreferences.LABEL_IGNORE_UNMATCHED_WITNESS_ENTRIES);
		mStats = new ExtractionStatistics();
	}

	public void setAST(final IASTTranslationUnit inputTU) {
		mTranslationUnit = inputTU;
	}

	/**
	 * Get the witness entries, i.e. a relation that maps each {@link IASTNode} to the {@link IExtractedWitnessEntry}s
	 * that match this location.
	 */
	public IExtractedCorrectnessWitness getWitness() {
		if (mResult == null) {
			if (!isReady()) {
				mLogger.warn("Cannot extract witness if there is no witness");
				return null;
			}
			mResult = extractWitness();
			printWitness();
		}
		return mResult;
	}

	private void printWitness() {
		final List<String> entriesAsString = mResult.printAllEntries();
		if (entriesAsString.isEmpty()) {
			mLogger.info("Witness did not contain any usable entries.");
			return;
		}
		mLogger.info("Found the following entries in the witness:");
		entriesAsString.forEach(mLogger::info);
	}

	protected abstract boolean isReady();

	/**
	 * Extract the witness, i.e. return an object that provides {@link IExtractedWitnessEntry}s that match a given
	 * {@link IASTNode}.
	 */
	protected abstract IExtractedCorrectnessWitness extractWitness();

	public static final class ExtractionStatistics {
		private int mSuccess;
		private int mFailure;

		public ExtractionStatistics() {
			mSuccess = 0;
			mFailure = 0;
		}

		public void success() {
			mSuccess++;
		}

		public void fail() {
			mFailure++;
		}

		public int getSuccess() {
			return mSuccess;
		}

		public int getFailure() {
			return mFailure;
		}

		public int getTotal() {
			return mSuccess + mFailure;
		}

		@Override
		public String toString() {
			return "T/S/F " + getTotal() + "/" + getSuccess() + "/" + getFailure();
		}
	}
}
