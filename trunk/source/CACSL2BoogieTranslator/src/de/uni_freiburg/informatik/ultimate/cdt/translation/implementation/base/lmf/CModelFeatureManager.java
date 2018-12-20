package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.lmf;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;

public class CModelFeatureManager {

	private final Map<CModelFeature, ICModelFeatureDefinition> mRequiredFeatures;

	public CModelFeatureManager() {
		mRequiredFeatures = new LinkedHashMap<>();

	}

	public void require(final CModelFeature feature) {
		if (mRequiredFeatures.containsKey(feature)) {
			return;
		}
		mRequiredFeatures.put(feature, null);
	}

	public ICModelFeatureDefinition getDefinition(final CModelFeature feature) {
		final ICModelFeatureDefinition definition = mRequiredFeatures.get(feature);
		if (definition == null) {
			final Class<? extends ICModelFeatureDefinition> clazz = feature.getDefinitionClass();
			final ICModelFeatureDefinition instance = ReflectionUtil.instantiate(clazz);
			mRequiredFeatures.put(feature, instance);
			return instance;
		}
		return definition;
	}

}
