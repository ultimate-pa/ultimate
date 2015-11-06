package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collections;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class AbstractInterpretationObserver implements IUnmanagedObserver {

	private static final boolean COMPMODE = true;
	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;

	public AbstractInterpretationObserver(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(AIActivator.PLUGIN_ID);
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) throws Throwable {

	}

	@Override
	public void finish() throws Throwable {

	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof RootNode) {
			final IProgressAwareTimer timer;
			if (COMPMODE) {
				// TODO: Hack s.t. we only take 20% of the remaining time
				timer = mServices.getProgressMonitorService().getChildTimer(0.2);
			} else {
				timer = mServices.getProgressMonitorService();
			}
			final AbstractInterpreter abstractInterpreter = new AbstractInterpreter(mServices, timer, COMPMODE);
			try {
				abstractInterpreter.processRcfg((RootNode) root);
			} catch (OutOfMemoryError oom) {
				throw oom;
			} catch (Throwable t) {
				mLogger.fatal("Exception during AIMK2 run: " + t.getMessage());
				if (!COMPMODE) {
					throw t;
				}
			}
			if (!COMPMODE) {
				dumpPredsToFile(root);
			}

			return false;
		}
		return true;
	}

	private void dumpPredsToFile(IElement root) {
		final AbstractInterpretationPredicates predsAnnnot = AbstractInterpretationPredicates.getAnnotation(root);
		final Map<RCFGNode, Term> preds;
		if (predsAnnnot != null) {
			preds = predsAnnnot.getPredicates();
		} else {
			preds = Collections.emptyMap();
		}
		dumpToFile(preds);
	}

	private void dumpToFile(Map<RCFGNode, Term> map) {
		StringBuilder sb = new StringBuilder();

		for (Entry<RCFGNode, Term> entry : map.entrySet()) {
			sb.append(entry.getValue()).append("\n");
		}
		if (sb.length() == 0) {
			sb.append("No preds :(\n");
		}

		String filePath = "F:/repos/ultimate/trunk/source/UltimateTest/target/surefire-reports/de.uni_freiburg.informatik.ultimatetest.suites.evals.AbstractInterpretationMk2TestSuite/preds.txt";
		sb.append("\n\n");
		try {
			BufferedWriter bw = new BufferedWriter(new FileWriter(filePath, true));
			bw.append(sb);
			bw.close();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}
}
