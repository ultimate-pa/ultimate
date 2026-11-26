package de.uni_freiburg.informatik.ultimate.eca2boogie;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/** Plugin entry point for the ECA-to-Boogie translation. */
public final class EcaToBoogie implements IGenerator {
	private static final String PLUGIN_ID = EcaToBoogie.class.getPackageName();
	private static final String PLUGIN_NAME = "ECA to Boogie";

	private ModelType mInputDefinition;
	private EcaToBoogieObserver mObserver;

	@Override
	public void init() {
		// Nothing to initialize
	}

	@Override
	public void finish() {
		// Nothing to release
	}

	@Override
	public String getPluginName() {
		return PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return PLUGIN_ID;
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		// No services are needed by the skeleton yet.
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.SOURCE;
	}

	@Override
	public List<String> getDesiredToolIds() {
		return List.of();
	}

	@Override
	public void setInputDefinition(final ModelType inputDefinition) {
		mInputDefinition = inputDefinition;
	}

	@Override
	public ModelType getOutputDefinition() {
		return new ModelType(getPluginID(), ModelType.Type.AST,
				mInputDefinition == null ? List.of() : mInputDefinition.getFileNames());
	}

	@Override
	public List<IObserver> getObservers() {
		mObserver = new EcaToBoogieObserver();
		return List.of(mObserver);
	}

	@Override
	public IElement getModel() {
		return mObserver == null ? null : mObserver.getUnit();
	}
}
