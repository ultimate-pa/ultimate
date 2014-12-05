package de.uni_freiburg.informatik.ultimate.ltl2aut;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.ltl2aut.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;

public class LTL2aut implements IGenerator {

	protected List<String> mFileNames;
	private boolean mProcess;
	private boolean mSkip;
	private int mUseful;

	private LTL2autObserver mObserver;
	private IUltimateServiceProvider mServices;
	private IToolchainStorage mStorage;

	public LTL2aut() {
		mFileNames = new ArrayList<String>();
	}

	@Override
	public void init() {
		mProcess = false;
		mUseful = 0;
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
	public GraphType getOutputDefinition() {
		List<String> filenames = new ArrayList<String>();
		filenames.add("Hardcoded");

		return new GraphType(Activator.PLUGIN_ID, GraphType.Type.AST, filenames);
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		if (mSkip) {
			return QueryKeyword.LAST;
		}
		return QueryKeyword.ALL;
	}

	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		switch (graphType.getCreator()) {
		case "de.uni_freiburg.informatik.ultimate.boogie.parser":
		case "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator":
			mProcess = true;
			mUseful++;
			break;
		default:
			mProcess = false;
			break;
		}
	}

	@Override
	public List<IObserver> getObservers() {
		mObserver = new LTL2autObserver(mServices, mStorage);
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		if (mProcess && !mSkip) {
			observers.add(mObserver);
		}
		return observers;
	}

	@Override
	public IElement getModel() {
		return mObserver.getNWAContainer();
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		mStorage = storage;
	}

	@SuppressWarnings("rawtypes")
	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
		Collection<CounterExampleResult> cex = CoreUtil.filterResults(services.getResultService().getResults(),
				CounterExampleResult.class);
		mSkip = !cex.isEmpty();
	}

	@Override
	public void finish() {
		if (!mSkip && mUseful == 0) {
			throw new IllegalStateException("Was used in a toolchain were it did nothing");
		}
		if (mSkip) {
			mServices.getLoggingService().getLogger(getPluginID())
					.info("Another plugin discovered errors, skipping...");
		}
	}

}
