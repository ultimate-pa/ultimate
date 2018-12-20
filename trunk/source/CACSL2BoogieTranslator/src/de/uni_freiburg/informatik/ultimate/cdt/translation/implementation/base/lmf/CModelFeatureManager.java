/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.lmf;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CModelFeatureManager {

	private final Map<CModelFeature, ICModelFeatureDefinition> mRequiredFeatures;

	public CModelFeatureManager() {
		mRequiredFeatures = new LinkedHashMap<>();
	}

	public void require(final CModelFeature feature, final Object... featureParams) {
		if (featureParams == null || featureParams.length == 0) {
			if (mRequiredFeatures.containsKey(feature)) {
				return;
			}
			mRequiredFeatures.put(feature, null);
		} else {
			final ICModelFeatureDefinition def = getDefinition(feature);
			def.addFeatureParameter(featureParams);
		}
	}

	public ICModelFeatureDefinition getDefinition(final CModelFeature feature) {
		final ICModelFeatureDefinition definition = mRequiredFeatures.get(feature);
		if (definition == null) {
			final Class<? extends ICModelFeatureDefinition> clazz = feature.getDefinitionClass();
			if (clazz == null) {
				throw new AssertionError("This feature has not definition: " + feature);
			}
			final ICModelFeatureDefinition instance = ReflectionUtil.instantiate(clazz);
			mRequiredFeatures.put(feature, instance);
			return instance;
		}
		return definition;
	}

}
