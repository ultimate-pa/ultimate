package de.uni_freiburg.informatik.ultimate.reachingdefinitions.plugin;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.rcfg.ReachDefRCFG;

public class ReachingDefinitions implements IAnalysis {

	private GraphType mCurrentGraphType;


	@Override
	public GraphType getOutputDefinition() {
		return mCurrentGraphType;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		mCurrentGraphType = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		switch (mCurrentGraphType.getCreator()) {
		case "RCFGBuilder":
			return Collections.singletonList((IObserver) new ReachDefRCFG());
		default:
			return Collections.emptyList();
		}
	}

	@Override
	public int init() {
		return 0;
	}

	@Override
	public String getName() {
		return Activator.PluginName;
	}

	@Override
	public String getPluginID() {
		return Activator.PluginName;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}

}
