package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.generalizers.InterpolantGeneralizer;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;

/**
 * Implementation of the IC3 algorithm and its variations<br/>
 * Input: The CFG of a program without function calls,
 *        restricted to linear rational arithmetic
 * @author leys
 */
public class IC3ModelCheckerObserver implements IUnmanagedObserver {
	
	protected static Logger 	s_logger 			= UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	private CFGExplicitNode		m_graphroot 		= null;
	private Script 				m_script 			= null;
	private IEclipsePreferences m_prefs				= null;
	private boolean 			m_madeChanges		= false;
	
	@Override
	public boolean process(IElement root) {
		System.err.println("Logger im Debug-Modus: " + s_logger.isDebugEnabled());
		m_graphroot		= (CFGExplicitNode)root;
		m_script		= m_graphroot.getScript();
		m_prefs = ConfigurationScope.INSTANCE.getNode(Activator.PLUGIN_ID);
		treeIC3();
		return false;
	}
	
	private void treeIC3() {
		// Unwind CFG into an ART
		MathPrinter.init();
		if (m_graphroot.getOutgoingNodes().size() != 1) {
			throw new RuntimeException("Kann nur genau eine Funktion behandeln!");
		}
		else {
			CFGExplicitNode cfgFunctionRoot = (CFGExplicitNode) m_graphroot.getOutgoingNodes().get(0);
			TreeIC3 treeIC3 = new TreeIC3(cfgFunctionRoot, m_script, s_logger,
											new InterpolantGeneralizer(), true);
			boolean result = treeIC3.start();
			if (result)
				reportResult(new PositiveResult<CFGExplicitNode>(cfgFunctionRoot, Activator.PLUGIN_ID, null, cfgFunctionRoot.getPayload().getLocation()));
			else
				reportResult(new CounterExampleResult<CFGExplicitNode>(cfgFunctionRoot, Activator.PLUGIN_ID, null, cfgFunctionRoot.getPayload().getLocation(), null));
		}

	}
	
	
	private static void reportResult(IResult res) {
		UltimateServices.getInstance().reportResult(Activator.PLUGIN_ID, res);
	}
	
	
	@Override
	public void finish() {
		// TODO Auto-generated method stub
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub
	}

	@Override
	public boolean performedChanges() {
		return m_madeChanges;
	}
}
