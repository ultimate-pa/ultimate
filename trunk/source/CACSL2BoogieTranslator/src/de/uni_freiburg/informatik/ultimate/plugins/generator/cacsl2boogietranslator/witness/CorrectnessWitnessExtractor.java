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

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.witnessparser.preferences.WitnessParserPreferences;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class CorrectnessWitnessExtractor {

	private final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;
	protected final boolean mCheckOnlyLoopInvariants;

	protected IASTTranslationUnit mTranslationUnit;
	private Map<IASTNode, ExtractedWitnessInvariant> mAST2Invariant;
	protected ExtractionStatistics mStats;

	public CorrectnessWitnessExtractor(final IUltimateServiceProvider service) {
		mServices = service;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCheckOnlyLoopInvariants = WitnessParserPreferences.getPrefs(service)
				.getBoolean(WitnessParserPreferences.LABEL_CW_USE_ONLY_LOOPINVARIANTS);
		mStats = new ExtractionStatistics();
	}

	public void setAST(final IASTTranslationUnit inputTU) {
		mTranslationUnit = inputTU;
	}

	/**
	 * @return a map from {@link IASTNode} to an {@link ExtractedWitnessInvariant}. The
	 *         {@link ExtractedWitnessInvariant} represents a witness invariant which has to hold before, at, or after
	 *         the {@link IASTNode}.
	 */
	public Map<IASTNode, ExtractedWitnessInvariant> getCorrectnessWitnessInvariants() {
		if (mAST2Invariant == null) {
			if (!isReady()) {
				mLogger.warn("Cannot extract witness if there is no witness");
				return null;
			}
			if (mCheckOnlyLoopInvariants) {
				mLogger.info("Only extracting loop invariants from correctness witness");
			} else {
				mLogger.info("Extracting all invariants from correctness witness");
			}
			mAST2Invariant = extract();
			printResults(mAST2Invariant);
		}
		return mAST2Invariant;
	}

	private void printResults(final Map<IASTNode, ExtractedWitnessInvariant> result) {
		if (result.isEmpty()) {
			mLogger.info("Witness did not contain any usable invariants.");
			return;
		}
		mLogger.info("Found the following invariants in the witness:");
		for (final Entry<IASTNode, ExtractedWitnessInvariant> entry : result.entrySet()) {
			assert entry.getKey() == entry.getValue().getRelatedAstNode();
			mLogger.info(entry.getValue().toStringWithWitnessNodeLabel());
		}
	}

	protected abstract boolean isReady();

	protected abstract Map<IASTNode, ExtractedWitnessInvariant> extract();

	protected Map<IASTNode, ExtractedWitnessInvariant> mergeMatchesIfNecessary(
			final Map<IASTNode, ExtractedWitnessInvariant> mapA, final Map<IASTNode, ExtractedWitnessInvariant> mapB) {
		if (mapA == null || mapA.isEmpty()) {
			return mapB;
		}
		if (mapB == null || mapB.isEmpty()) {
			return mapA;
		}

		final Map<IASTNode, ExtractedWitnessInvariant> rtr = new HashMap<>(mapA.size());
		for (final Entry<IASTNode, ExtractedWitnessInvariant> entryB : mapB.entrySet()) {
			final ExtractedWitnessInvariant aWitnessInvariant = mapA.get(entryB.getKey());
			if (aWitnessInvariant == null) {
				rtr.put(entryB.getKey(), entryB.getValue());
			} else {
				rtr.put(entryB.getKey(), mergeAndWarn(aWitnessInvariant, entryB.getValue()));
			}
		}
		for (final Entry<IASTNode, ExtractedWitnessInvariant> entryA : mapA.entrySet()) {
			final ExtractedWitnessInvariant aWitnessInvariant = mapB.get(entryA.getKey());
			if (aWitnessInvariant == null) {
				rtr.put(entryA.getKey(), entryA.getValue());
			} else {
				// we already merged in the earlier pass
			}
		}
		return rtr;
	}

	private ExtractedWitnessInvariant mergeAndWarn(final ExtractedWitnessInvariant invA,
			final ExtractedWitnessInvariant invB) {
		final ExtractedWitnessInvariant newInvariant = invA.merge(invB);
		mLogger.warn("Merging invariants");
		mLogger.warn("  Invariant A is " + invA.toString());
		mLogger.warn("  Invariant B is " + invB.toString());
		mLogger.warn("  New match: " + newInvariant.toString());
		return newInvariant;
	}

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
