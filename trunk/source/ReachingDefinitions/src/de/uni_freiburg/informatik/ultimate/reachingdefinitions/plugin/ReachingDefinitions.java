package de.uni_freiburg.informatik.ultimate.reachingdefinitions.plugin;

import java.util.Collections;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.rcfg.ReachDefRCFG;
import de.uni_freiburg.informatik.ultimate.reachingdefinitions.trace.ReachDefTrace;

public class ReachingDefinitions implements IAnalysis {

	private GraphType mCurrentGraphType;
	private IUltimateServiceProvider mServices;

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
			return Collections.singletonList((IObserver) new ReachDefRCFG(mServices.getLoggingService().getLogger(
					Activator.PluginID)));
		default:
			return Collections.emptyList();
		}
	}

	@Override
	public int init() {
		return 0;
	}

	@Override
	public String getPluginName() {
		return Activator.PluginName;
	}

	@Override
	public String getPluginID() {
		return Activator.PluginID;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}

	public static CodeBlock[] computeRDForTrace(CodeBlock[] trace, Logger logger) throws Throwable {
		ReachDefTrace rdt = new ReachDefTrace(logger);
		rdt.process(trace);
		return trace;
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
	}

}
