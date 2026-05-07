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

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.model.IAnalysis;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.proofs.ProofAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;

/**
 * This class initializes the Civlizer.
 *
 * @author Dominik Klumpp (klumpp@lix.polytechnique.fr)
 *
 */
public class Civlizer implements IAnalysis, IUnmanagedObserver {
	private IUltimateServiceProvider mServices;
	private ILogger mLogger;

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
		return null; // new PreferenceInitializer();
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Civlizer.class);
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

		if (root instanceof final Unit boogieFile && root instanceof final BoogieIcfgContainer icfg) {

			mLogger.warn(Translator.translate(boogieFile));

			// not working not printed
			mLogger.warn("TEST TEST TEST");
			final var proofs = ProofAnnotation.getProofs(icfg, OwickiGriesAnnotation.class);
			mLogger.warn(proofs);
			mLogger.warn("TEST TEST TEST");
		}

		return false;
	}
}
