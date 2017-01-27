/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptInterpreter plug-in.
 * 
 * The ULTIMATE AutomataScriptInterpreter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptInterpreter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptInterpreter plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptInterpreter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AutomataScriptInterpreter plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Automaton2UltimateModel;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * Auto-Generated Stub for the plug-in's Observer.
 */
public class AutomataScriptInterpreterObserver implements IUnmanagedObserver {
	private final ILogger mLogger;
	
	private IElement mGraphrootOfUltimateModelOfLastPrintedAutomaton;
	
	private final IUltimateServiceProvider mServices;
	
	/**
	 * @param services
	 *            Ultimate services.
	 */
	public AutomataScriptInterpreterObserver(final IUltimateServiceProvider services) {
		assert services != null;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}
	
	@Override
	public boolean process(final IElement root) {
		
		AssignableTest.initPrimitiveTypes();
		final TestFileInterpreter ti = new TestFileInterpreter(mServices);
		ti.interpretTestFile((AtsASTNode) root);
		
		IAutomaton<?, ?> printAutomaton = ti.getLastPrintedAutomaton();
		if (printAutomaton == null) {
			printAutomaton = getDummyAutomatonWithMessage();
		}
		try {
			mGraphrootOfUltimateModelOfLastPrintedAutomaton =
					Automaton2UltimateModel.ultimateModel(new AutomataLibraryServices(mServices), printAutomaton);
		} catch (final AutomataOperationCanceledException e) {
			mLogger.warn("Nothing visualized because of timeout");
		}
		return false;
	}
	
	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}
	
	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
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
		final NestedWordAutomaton<String, String> dummyAutomaton = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), new HashSet<String>(0), null, null, new StringFactory());
		dummyAutomaton.addState(true, false, "Use the print keyword in .ats file to select an automaton"
				+ " for visualization");
		return dummyAutomaton;
	}
}
