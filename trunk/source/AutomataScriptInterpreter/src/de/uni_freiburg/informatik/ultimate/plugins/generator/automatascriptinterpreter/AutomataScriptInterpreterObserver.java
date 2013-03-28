package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.Automaton2UltimateModel;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;


/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class AutomataScriptInterpreterObserver implements IUnmanagedObserver {

	IElement m_GraphrootOfUltimateModelOfLastPrintedAutomaton;
	
	@Override
	public boolean process(IElement root) {
		TestFileInterpreter ti = new TestFileInterpreter();
		ti.interpretTestFile((AtsASTNode)root);
		m_GraphrootOfUltimateModelOfLastPrintedAutomaton = 
				Automaton2UltimateModel.ultimateModel(null);
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

	

	
	
}
