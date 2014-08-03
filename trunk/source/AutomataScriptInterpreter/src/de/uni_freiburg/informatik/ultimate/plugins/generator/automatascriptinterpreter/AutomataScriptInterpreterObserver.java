package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.Automaton2UltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.ExampleNWAFactory;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class AutomataScriptInterpreterObserver implements IUnmanagedObserver {

	private Logger mLogger;

	IElement mGraphrootOfUltimateModelOfLastPrintedAutomaton;

	private IUltimateServiceProvider mServices;

	public AutomataScriptInterpreterObserver(IUltimateServiceProvider services) {
		assert services != null;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

	@Override
	public boolean process(IElement root) {
		
		//TODO: Now you can get instances of your library classes for the current toolchain like this: 
		//NWA is nevertheless very broken, as its static initialization prevents parallelism 
		//Surprisingly, this call lazily initializes the static fields of NWA Lib and, like magic, the toolchain works ...
		mServices.getServiceInstance(ExampleNWAFactory.class);
		
		AssignableTest.initPrimitiveTypes();
		TestFileInterpreter ti = new TestFileInterpreter(mServices);
		ti.interpretTestFile((AtsASTNode) root);

		IAutomaton<?, ?> printAutomaton = ti.getLastPrintedAutomaton();
		if (printAutomaton == null) {
			printAutomaton = getDummyAutomatonWithMessage();
		}
		try {
			mGraphrootOfUltimateModelOfLastPrintedAutomaton = Automaton2UltimateModel.ultimateModel(printAutomaton);
		} catch (OperationCanceledException e) {
			mLogger.warn("Nothing visualized because of timeout");
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
		return mGraphrootOfUltimateModelOfLastPrintedAutomaton;
	}

	public IAutomaton<String, String> getDummyAutomatonWithMessage() {
		NestedWordAutomaton<String, String> dummyAutomaton = new NestedWordAutomaton<String, String>(
				new HashSet<String>(0), null, null, new StringFactory());
		dummyAutomaton.addState(true, false, "Use the print keyword in .ats file to select an automaton"
				+ " for visualization");
		return dummyAutomaton;
	}

}
