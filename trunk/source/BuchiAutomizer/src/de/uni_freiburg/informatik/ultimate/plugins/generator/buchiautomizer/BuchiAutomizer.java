package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Collections;
import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;

/**
 * Main class of Plug-In BuchiAutomizer
 * 
 * 
 * TODO: refine comments
 * 
 */
public class BuchiAutomizer implements IGenerator {

	private static final String s_PLUGIN_NAME = Activator.s_PLUGIN_NAME;
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;

	private Logger mLogger;

	private BuchiAutomizerObserver mObserver;
	private GraphType mInputDefinition;
	private IUltimateServiceProvider mServices;
	private IToolchainStorage mStorage;

	@Override
	public String getPluginName() {
		return s_PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	@Override
	public void init() {
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	@Override
	public List<String> getDesiredToolID() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		this.mInputDefinition = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		if (programContainsErrors(mServices.getResultService())) {
			mLogger.info("Another Plugin discovered errors, I will " + "not analyze termination");
			return Collections.emptyList();
		} else {
			mLogger.info("Safety of program was proven or not checked, " + "starting termination analysis");
			mObserver = new BuchiAutomizerObserver(mServices, mStorage);
			return Collections.singletonList((IObserver) mObserver);
		}
	}

	@Override
	public GraphType getOutputDefinition() {
		/*
		 * TODO This generated method body only assumes a standard case. Adapt
		 * it if necessary. Otherwise remove this todo-tag.
		 */
		return new GraphType(Activator.s_PLUGIN_ID, mInputDefinition.getType(), mInputDefinition.getFileNames());
	}

	@Override
	public IElement getModel() {
		if (mObserver != null) {
			return mObserver.getModel();
		}
		return null;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

	private boolean programContainsErrors(IResultService service) {
		for (Entry<String, List<IResult>> entry : service.getResults().entrySet()) {
			for (IResult resul : entry.getValue()) {
				if (resul instanceof CounterExampleResult) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		mStorage = storage;
	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);

	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}
}
