package de.uni_freiburg.informatik.ultimate.plugins.generator.automatalibraryrandomizedtests;


import java.io.File;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter.Labeling;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementRE;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementSVW;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.GetRandomNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.ReachableStatesCopy;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.BuchiReduce;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.automatalibraryrandomizedtests.preferences.PreferenceConstants;



/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class AutomataLibraryRandomizedTestsObserver implements IUnmanagedObserver {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	private static UltimateServices s_UltiServ = UltimateServices.getInstance();
	
	@Override
	public boolean process(IElement root) {
		// TODO Auto-generated method stub
		s_Logger.warn("Starting randomized automat tests. Press cancel to stop the tests.");
		
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode(Activator.s_PLUGIN_ID);
		boolean writeToFile = prefs.getBoolean(PreferenceConstants.Name_WriteToFile, PreferenceConstants.Default_WriteToFile);
		String operation = prefs.get(PreferenceConstants.Name_Operation, PreferenceConstants.Default_Operation);
		
		int numberLetters = prefs.getInt(PreferenceConstants.Name_NumberOfLetters, PreferenceConstants.Default_NumberOfLetters);
		int numberStates = prefs.getInt(PreferenceConstants.Name_NumberOfStates, PreferenceConstants.Default_NumberOfStates);
		int initialPerMille = prefs.getInt(PreferenceConstants.Name_ProbabilityInitial, PreferenceConstants.Default_ProbabilityInitial);
		int finalPerMille = prefs.getInt(PreferenceConstants.Name_ProbabilityFinal, PreferenceConstants.Default_ProbabilityFinal);
		int internalPerMille = prefs.getInt(PreferenceConstants.Name_ProbabilityInternalTransition, PreferenceConstants.Default_ProbabilityInternalTransition);
		int callPerMille = prefs.getInt(PreferenceConstants.Name_ProbabilityCallTransition, PreferenceConstants.Default_ProbabilityCallTransition);
		int returnPerMille = prefs.getInt(PreferenceConstants.Name_ProbabilityReturnTransition, PreferenceConstants.Default_ProbabilityReturnTransition);
		
		double probInitial = initialPerMille / 1000.0;
		double probFinal = finalPerMille / 1000.0;
		double probInternal = internalPerMille / 1000.0;
		double probCall = callPerMille / 1000.0;
		double probReturn = returnPerMille / 1000.0;
		
		try {
			
			int i = 0;
			while (UltimateServices.getInstance().continueProcessing()) {
				INestedWordAutomaton<String, String> auto = (new GetRandomNwa(numberLetters, numberStates, probInternal, probCall, probReturn, probFinal)).getResult();
				s_Logger.info("Generated an automaton which has " + auto.sizeInformation());
				if (writeToFile) {
					String directory = getDirectory();
					String filename = directory + File.separator+"Random" + i;
					new AtsDefinitionPrinter<String, String>(auto, filename, Labeling.QUOTED, "");
				}
				
				if (operation.equals("buchiComplementSVW")) {
					INestedWordAutomaton<String, String> resultSVW = (new BuchiComplementSVW<String, String>(auto)).getResult();					
				} else if (operation.equals("minimizeSevpa")) {
					(new MinimizeSevpa<String, String>(auto)).getResult();
				} else if (operation.equals("buchiComplementComparison")) {
					BuchiComplementRE<String, String> bcre = new BuchiComplementRE<String, String>(auto);
					if (bcre.applicable()) {
						INestedWordAutomaton<String, String> resultRE = bcre.getResult();
						s_Logger.info("ResultRE states: " + resultRE.size());
						resultRE =(new BuchiReduce<String, String>(resultRE)).getResult();
						s_Logger.info("ResultRE states after size reduction: " + resultRE.size());
					} else {
						s_Logger.info("buchiComplementRE not applicable");
					}

					INestedWordAutomaton<String, String> resultFKV = (new BuchiComplementFKV<String, String>(auto)).getResult();
					s_Logger.info("ResultFKV states: " + resultFKV.size());
					resultFKV =(new ReachableStatesCopy<String, String>(resultFKV, false, false, false, true)).getResult();
					s_Logger.info("ResultFKV states after remove of non-live states: " + resultFKV.size());
					resultFKV =(new BuchiReduce<String, String>(resultFKV)).getResult();
					s_Logger.info("ResultFKV states after size reduction: " + resultFKV.size());

					INestedWordAutomaton<String, String> resultSVW = (new BuchiComplementSVW<String, String>(auto)).getResult();
					s_Logger.warn("ResultSVW states: " + resultSVW.size());
					resultSVW =(new ReachableStatesCopy<String, String>(resultSVW, false, false, false, true)).getResult();
					s_Logger.info("ResultSVW states after remove of non-live states: " + resultSVW.size());
					resultSVW =(new BuchiReduce<String, String>(resultSVW)).getResult();
					s_Logger.info("ResultSVW states after size reduction: " + resultSVW.size());

				} else {
					throw new IllegalArgumentException("unknown test");
				}
				i++;
			}
			
		} catch (OperationCanceledException e) {
			s_Logger.warn("RandomizedTesting Cancelled");
		}
		
		
		return false;
	}
	
	
	private String getDirectory() {
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode("NestedWordAutomata");
		String directory = prefs.get(
				de.uni_freiburg.informatik.ultimate.automata.preferences.PreferenceConstants.Name_Path, 
				de.uni_freiburg.informatik.ultimate.automata.preferences.PreferenceConstants.Default_Path);
		return directory;
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
