/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2013-2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 *
 * This file is part of the ULTIMATE BlockEncodingV2 plug-in.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncodingV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncodingV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncodingV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtransformation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtransformation.preferences.IcfgTransformationPreferences;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class IcfgTransformation implements IGenerator {

	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;
	private static final XnfConversionTechnique XNF_CONVERSION_TECHNIQUE =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private ILogger mLogger;
	private IcfgTransformationObserver mObserver;
	private IUltimateServiceProvider mServices;
	private IcfgTransformationBacktranslator mBacktranslator;
	private ModelType mOldGraphType;

	@Override
	public ModelType getOutputDefinition() {
		return new ModelType(Activator.PLUGIN_ID, ModelType.Type.CFG, mOldGraphType.getFileNames());
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.LAST;
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		mOldGraphType = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		final List<IObserver> observers = new ArrayList<>();
		mObserver = new IcfgTransformationObserver(mLogger, mServices, mBacktranslator, SIMPLIFICATION_TECHNIQUE,
				XNF_CONVERSION_TECHNIQUE);
		observers.add(mObserver);
		return observers;
	}

	@Override
	public void init() {
		// not needed
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public IElement getModel() {
		return mObserver.getModel();
	}

	@Override
	public List<String> getDesiredToolIds() {
		return Collections.emptyList();
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new IcfgTransformationPreferences();
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage storage) {
		// not needed
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mBacktranslator = new IcfgTransformationBacktranslator(IcfgEdge.class, Term.class, mLogger);
		mServices.getBacktranslationService().addTranslator(mBacktranslator);
	}

	@Override
	public void finish() {
		// not needed
	}

}
