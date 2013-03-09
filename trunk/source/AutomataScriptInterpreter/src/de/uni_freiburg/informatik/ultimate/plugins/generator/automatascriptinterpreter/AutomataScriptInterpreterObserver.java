package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;
import java.io.File;
import java.lang.reflect.Method;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.FileLocator;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;


/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class AutomataScriptInterpreterObserver implements IUnmanagedObserver {

	
	@Override
	public boolean process(IElement root) {
		TestFileInterpreter ti = new TestFileInterpreter();
		try {
			ti.interpretTestFile((AtsASTNode)root);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
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

	

	
	
}
