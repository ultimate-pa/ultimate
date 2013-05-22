package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.Automaton2UltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;


/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class AutomataScriptInterpreterObserver implements IUnmanagedObserver {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	IElement m_GraphrootOfUltimateModelOfLastPrintedAutomaton;
	
	@Override
	public boolean process(IElement root) {
		AssignableTest.initPrimitiveTypes();
		TestFileInterpreter ti = new TestFileInterpreter();
		ti.interpretTestFile((AtsASTNode) root);

		IAutomaton<?, ?> printAutomaton = ti.getLastPrintedAutomaton();
		if (printAutomaton == null) {
			printAutomaton = getDummyAutomatonWithMessage();
		}
		try {
			m_GraphrootOfUltimateModelOfLastPrintedAutomaton = 
					Automaton2UltimateModel.ultimateModel(printAutomaton);
		} catch (OperationCanceledException e) {
			s_Logger.warn("Nothing visualized because of timeout");
		}
		return false;
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
		// TODO Auto-generated method stub
		return false;
	}
	
	IElement getUltimateModelOfLastPrintedAutomaton() {
		return m_GraphrootOfUltimateModelOfLastPrintedAutomaton;
	}

	public IAutomaton<String,String> getDummyAutomatonWithMessage() {
		NestedWordAutomaton<String,String> dummyAutomaton = 
			new NestedWordAutomaton<String,String>(
					new HashSet<String>(0), null, null, new StringFactory());
		dummyAutomaton.addState(true, false,
			"Use the print keyword in .ats file to select an automaton" +
			" for visualization");
		return dummyAutomaton;
	}
	
}
