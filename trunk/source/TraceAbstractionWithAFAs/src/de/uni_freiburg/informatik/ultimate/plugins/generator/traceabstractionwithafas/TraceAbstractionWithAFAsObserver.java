package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionwithafas;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionBenchmarks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class TraceAbstractionWithAFAsObserver extends BaseObserver {

	private final Logger mLogger;

	/**
	 * Root Node of this Ultimate model. I use this to store information that
	 * should be passed to the next plugin. The Successors of this node exactly
	 * the initial nodes of procedures.
	 */
	private IElement m_graphroot = null;

	private final IUltimateServiceProvider mServices;

	public TraceAbstractionWithAFAsObserver(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

	@Override
	public boolean process(IElement root) {

		RootNode rootNode = (RootNode) root;
		RootAnnot rootAnnot = rootNode.getRootAnnot();
		SmtManager smtManager = new SmtManager(rootAnnot.getBoogie2SMT(), rootAnnot.getModGlobVarManager(), mServices);
		TraceAbstractionBenchmarks taBenchmarks = new TraceAbstractionBenchmarks(rootAnnot);
		TAPreferences taPrefs = new TAPreferences();

		Map<String, Collection<ProgramPoint>> proc2errNodes = rootAnnot.getErrorNodes();
		Collection<ProgramPoint> errNodesOfAllProc = new ArrayList<ProgramPoint>();
		for (Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}

		PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(root);
		if (pa == null || pa.getSymbolTable() == null) {
			String errorMsg = "No symbol table found on given RootNode.";
			mLogger.fatal(errorMsg);
			throw new UnsupportedOperationException(errorMsg);
		}

		TAwAFAsCegarLoop cegarLoop = new TAwAFAsCegarLoop("bla", rootNode, smtManager, taBenchmarks, taPrefs,
				errNodesOfAllProc, taPrefs.interpolation(), taPrefs.computeHoareAnnotation(), mServices,
				pa.getSymbolTable());

		Result result = cegarLoop.iterate();

		return false;
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRoot() {
		return m_graphroot;
	}

}
