/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer;

import java.io.File;
import java.io.PrintWriter;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.civlizer.preferences.CivlizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.lib.util.FilePrinterUtils;
import de.uni_freiburg.informatik.ultimate.core.model.IAnalysis;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.icfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.lib.proofs.ProofAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;

/**
 * This class initializes the Civlizer.
 *
 * @author Dominik Klumpp (klumpp@lix.polytechnique.fr)
 *
 */
public class Civlizer implements IAnalysis, IUnmanagedObserver {
	private IUltimateServiceProvider mServices;
	private ILogger mLogger;
	private IPreferenceProvider mPrefs;

	private ProgramAndProof mProgramAndProof;
	private boolean mProcessed;

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public void init() {
		// not needed
		mProgramAndProof = new ProgramAndProof(mServices);
	}

	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.ALL;
	}

	/**
	 * I don't need a special tool
	 */
	@Override
	public List<String> getDesiredToolIds() {
		return Collections.emptyList();
	}

	@Override
	public ModelType getOutputDefinition() {
		/* use old graph type definition */
		return null;
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		// not required.
	}

	@Override
	public List<IObserver> getObservers() {
		return List.of(this);
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new CivlizerPreferenceInitializer();
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Civlizer.class);
		mPrefs = services.getPreferenceProvider(Activator.PLUGIN_ID);
	}

	@Override
	public void finish() {
		// not needed
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels)
			throws Throwable {
		// do nothing
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (root instanceof final Unit boogieFile) {
			mProgramAndProof.setBoogieAst(boogieFile);
			mLogger.warn(boogieFile);
		}

		if (root instanceof final BoogieIcfgContainer icfg) {
			// TODO useful for debugging, but remove the following 2 lines before merging
			final List<OwickiGriesAnnotation> proof = ProofAnnotation.getProofs(icfg, OwickiGriesAnnotation.class);
			mLogger.warn(proof);

			mProgramAndProof.setIcfg(icfg);
		}

		if (mProgramAndProof.isFull() && !mProcessed) {
			mProcessed = true;
			final Translator translation = new Translator(mServices, mProgramAndProof);

			final var outputFileSettings = FilePrinterUtils.OutputFileSettings.fromPrinterPreferences(mPrefs,
					"Civlizer_", "_UID", ".civl.bpl");
			final File outputFile = FilePrinterUtils.openOutputFile(outputFileSettings, root, mLogger);
			mLogger.info("Writing civlized program to %s", outputFile);
			try (final var printer = new CivlOutput(new PrintWriter(outputFile))) {
				printer.print(translation.getResult());
			}

			if (mPrefs.getBoolean(CivlizerPreferenceInitializer.LABEL_RUN_CIVL_ON_OUTPUT)) {
				final String workingDir = mPrefs.getString(CivlizerPreferenceInitializer.LABEL_CIVL_WORKING_DIRECTORY);
				final String civlCommand = mPrefs.getString(CivlizerPreferenceInitializer.LABEL_CIVL_COMMAND);
				final int timeout = mPrefs.getInt(CivlizerPreferenceInitializer.LABEL_CIVL_TIMEOUT);

				final var runner = new CivlRunner(mServices, Paths.get(workingDir), civlCommand, timeout);
				final var result = runner.runOnFile(outputFile);
				mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
			}
		}

		return false;
	}
}
