package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences;

import java.io.IOException;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.PreferenceValues.INTERPOLATION;

/**
 * this calls contributes to the extensionpoint:
 * org.eclipse.ui.prefgerencePages   see at the plugin.xml
 * 
 */
public class PreferencePage extends FieldEditorPreferencePage
		implements IWorkbenchPreferencePage {

	public static final Logger logger =  Logger.getLogger(PreferencePage.class);
	
	
	private static final ScopedPreferenceStore preferences = new ScopedPreferenceStore(InstanceScope.INSTANCE,Activator.PLUGIN_ID);

	public PreferencePage(){
		super(GRID);
//		preferences 
		setPreferenceStore(preferences);
	}
	//@Override
	//@Override
	protected void createFieldEditors() {
		
		BooleanFieldEditor interprodecural = new BooleanFieldEditor(
				PreferenceValues.NAME_INTERPROCEDUTAL,
				PreferenceValues.LABEL_INTERPROCEDUTAL,
				getFieldEditorParent());
		addField(interprodecural);
		
		BooleanFieldEditor simplifyCodeBlocks = new BooleanFieldEditor(
				PreferenceValues.NAME_simplifyCodeBlocks,
				PreferenceValues.LABEL_simplifyCodeBlocks,
				getFieldEditorParent());
		addField(simplifyCodeBlocks);
		
		BooleanFieldEditor errorsAtOnce = new BooleanFieldEditor(
				PreferenceValues.NAME_AllErrorsAtOnce,
				PreferenceValues.LABEL_AllErrorsAtOnce,
				getFieldEditorParent());
		addField(errorsAtOnce);
		
		
		BooleanFieldEditor preserveGotoEdges = new BooleanFieldEditor(
				PreferenceValues.NAME_PreserveGotoEdges,
				PreferenceValues.LABEL_PreserveGotoEdges,
				getFieldEditorParent());
		addField(preserveGotoEdges);
		
		ComboFieldEditor letter = new ComboFieldEditor(
				PreferenceValues.NAME_LETTER,
				PreferenceValues.LABEL_LETTER,
				new String[][]{{PreferenceValues.VALUE_LETTER_STATEMENT, PreferenceValues.VALUE_LETTER_STATEMENT},
						{PreferenceValues.VALUE_LETTER_SEQUENCE, PreferenceValues.VALUE_LETTER_SEQUENCE},
						{PreferenceValues.VALUE_LETTER_BLOCK, PreferenceValues.VALUE_LETTER_BLOCK}},
				getFieldEditorParent());
		addField(letter);
		
		ComboFieldEditor solver = new ComboFieldEditor(
				PreferenceValues.NAME_SOLVER,
				PreferenceValues.LABEL_SOLVER,
				new String[][]{{PreferenceValues.VALUE_SOLVER_SMTINTERPOL.toString(), PreferenceValues.VALUE_SOLVER_SMTINTERPOL.toString()},
						{PreferenceValues.VALUE_SOLVER_Z3.toString(), PreferenceValues.VALUE_SOLVER_Z3.toString()}},
				getFieldEditorParent());
		addField(solver);	
		
		IntegerFieldEditor timeout = new IntegerFieldEditor(
				PreferenceValues.NAME_TIMEOUT, 
				PreferenceValues.LABEL_TIMEOUT,	
				getFieldEditorParent(), 
				6);
		timeout.setValidRange(0, 1000000);
		addField(timeout);
		
		IntegerFieldEditor iterations = new IntegerFieldEditor(
				PreferenceValues.NAME_ITERATIONS, 
				PreferenceValues.LABEL_ITERATIONS,	
				getFieldEditorParent(), 
				6);
		iterations.setValidRange(0, 1000000);
		addField(iterations);

		ComboFieldEditor artifact = new ComboFieldEditor(
				PreferenceValues.NAME_ARTIFACT, 
				PreferenceValues.LABEL_ARTIFACT, 
				new String[][]{{PreferenceValues.VALUE_ABSTRACTION, PreferenceValues.VALUE_ABSTRACTION},
						{PreferenceValues.VALUE_INTERPOLANT_AUTOMATON, PreferenceValues.VALUE_INTERPOLANT_AUTOMATON},
						{PreferenceValues.VALUE_NEG_INTERPOLANT_AUTOMATON, PreferenceValues.VALUE_NEG_INTERPOLANT_AUTOMATON},
						{PreferenceValues.VALUE_RCFG, PreferenceValues.VALUE_RCFG}},
				getFieldEditorParent());
		addField(artifact);
		
		IntegerFieldEditor observedIterations = new IntegerFieldEditor(
				PreferenceValues.NAME_WATCHITERATION, 
				PreferenceValues.LABEL_OBSERVEDITERATION,
				getFieldEditorParent(),
				6);
		observedIterations.setValidRange(0, 10000000);
		addField(observedIterations);
		
		BooleanFieldEditor hoare = new BooleanFieldEditor(
				PreferenceValues.NAME_HOARE,
				PreferenceValues.LABEL_HOARE,
				getFieldEditorParent());
		addField(hoare); 
		
		ComboFieldEditor interpolants; {
			String[][] entryNamesAndValues = new String[INTERPOLATION.values().length][2];
			for (int i=0; i<INTERPOLATION.values().length; i++) {
				entryNamesAndValues[i][0] = INTERPOLATION.values()[i].toString();
				entryNamesAndValues[i][1] = INTERPOLATION.values()[i].toString();
			}
			interpolants = new ComboFieldEditor(
					PreferenceValues.NAME_INTERPOLATED_LOCS,
					PreferenceValues.LABEL_INTERPOLATED_LOCS, 
					entryNamesAndValues,
					getFieldEditorParent());
		}
		addField(interpolants);
		
		BooleanFieldEditor edges2True = new BooleanFieldEditor(
				PreferenceValues.NAME_EDGES2TRUE,
				PreferenceValues.LABEL_EDGES2TRUE,
				getFieldEditorParent());
		addField(edges2True); 

		ComboFieldEditor additionalEdges = new ComboFieldEditor(
				PreferenceValues.NAME_InterpolantAutomaton,
				PreferenceValues.LABEL_InterpolantAutomaton, 
				new String[][]{{PreferenceValues.VALUE_InterpolantAutomaton_SingleTrace, PreferenceValues.VALUE_InterpolantAutomaton_SingleTrace},
						{PreferenceValues.VALUE_InterpolantAutomaton_Canonical, PreferenceValues.VALUE_InterpolantAutomaton_Canonical},
						{PreferenceValues.VALUE_InterpolantAutomaton_TotalInterpolation, PreferenceValues.VALUE_InterpolantAutomaton_TotalInterpolation},
						{PreferenceValues.VALUE_InterpolantAutomaton_TwoTrack, PreferenceValues.VALUE_InterpolantAutomaton_TwoTrack}},
				getFieldEditorParent());
		addField(additionalEdges);

		BooleanFieldEditor dumpScript = new BooleanFieldEditor(
				PreferenceValues.NAME_DUMPSCRIPT,
				PreferenceValues.LABEL_DUMPSCRIPT,
				getFieldEditorParent());
		addField(dumpScript); 
		
		BooleanFieldEditor dumpFormulas = new BooleanFieldEditor(
				PreferenceValues.NAME_DUMPFORMULAS,
				PreferenceValues.LABEL_DUMPFORMULAS,
				getFieldEditorParent());
		addField(dumpFormulas); 
		
		BooleanFieldEditor dumpAutomata = new BooleanFieldEditor(
				PreferenceValues.NAME_DUMPAUTOMATA,
				PreferenceValues.LABEL_DUMPAUTOMATA,
				getFieldEditorParent());
		addField(dumpAutomata); 

		DirectoryFieldEditor dumpPath = new DirectoryFieldEditor(
				PreferenceValues.NAME_DUMPPATH,
				PreferenceValues.LABEL_DUMPPATH,
				getFieldEditorParent());
		addField(dumpPath);
		
		ComboFieldEditor determinization = new ComboFieldEditor(
				PreferenceValues.NAME_DETERMINIZATION,
				PreferenceValues.LABEL_DETERMINIZATION, 
				new String[][]{{PreferenceValues.VALUE_POWERSET,PreferenceValues.VALUE_POWERSET},
						{PreferenceValues.VALUE_BESTAPPROXIMATION, PreferenceValues.VALUE_BESTAPPROXIMATION},
						{PreferenceValues.VALUE_SELFLOOP, PreferenceValues.VALUE_SELFLOOP},
						{PreferenceValues.VALUE_STRONGESTPOST, PreferenceValues.VALUE_STRONGESTPOST},
						{PreferenceValues.VALUE_EAGERPOST, PreferenceValues.VALUE_EAGERPOST},
						{PreferenceValues.VALUE_LAZYPOST, PreferenceValues.VALUE_LAZYPOST}},
				getFieldEditorParent());
		addField(determinization);
		
		BooleanFieldEditor difference = new BooleanFieldEditor(
				PreferenceValues.NAME_DIFFERENCE_SENWA,
				PreferenceValues.LABEL_DIFFERENCE_SENWA,
				getFieldEditorParent());
		addField(difference);
		
		BooleanFieldEditor minimize = new BooleanFieldEditor(
				PreferenceValues.NAME_MINIMIZE,
				PreferenceValues.LABEL_MINIMIZE,
				getFieldEditorParent());
		addField(minimize);
		
		ComboFieldEditor concurrency = new ComboFieldEditor(
				PreferenceValues.NAME_CONCURRENCY,
				PreferenceValues.LABEL_CONCURRENCY, 
				new String[][]{{PreferenceValues.VALUE_FINITE_AUTOMATON,PreferenceValues.VALUE_FINITE_AUTOMATON},
						{PreferenceValues.VALUE_PETRI_NET, PreferenceValues.VALUE_PETRI_NET}},
				getFieldEditorParent());
		addField(concurrency);
		
		
		ComboFieldEditor order = new ComboFieldEditor(
				PreferenceValues.NAME_Order,
				PreferenceValues.LABEL_Order, 
				new String[][]{{PreferenceValues.VALUE_KMM,PreferenceValues.VALUE_KMM},
						{PreferenceValues.VALUE_EVR, PreferenceValues.VALUE_EVR},
						{PreferenceValues.VALUE_EVRMark, PreferenceValues.VALUE_EVRMark}},
				getFieldEditorParent());
		addField(order);
		
		BooleanFieldEditor cutOff = new BooleanFieldEditor(
				PreferenceValues.NAME_cutOff,
				PreferenceValues.LABEL_cutOff,
				getFieldEditorParent());
		addField(cutOff);
		
		BooleanFieldEditor unfolding2Net = new BooleanFieldEditor(
				PreferenceValues.NAME_unfolding2Net,
				PreferenceValues.LABEL_unfolding2Net,
				getFieldEditorParent());
		addField(unfolding2Net);
	

//		preferences.setDefault(PreferenceValues.NAME_INTERPROCEDUTAL, PreferenceValues.DEF_INTERPROCEDUTAL);
//		preferences.setDefault(PreferenceValues.NAME_SOLVER, PreferenceValues.DEF_SOLVER);
//		preferences.setDefault(PreferenceValues.NAME_ITERATIONS, PreferenceValues.DEF_ITERATIONS);
//		preferences.setDefault(PreferenceValues.NAME_HOARE, PreferenceValues.DEF_HOARE);
//		preferences.setDefault(PreferenceValues.NAME_ARTIFACT, PreferenceValues.DEF_ARTIFACT);
//		preferences.setDefault(PreferenceValues.NAME_WATCHITERATION, PreferenceValues.DEF_WATCHITERATION);
//		preferences.setDefault(PreferenceValues.NAME_INTERPOLATED_LOCS, PreferenceValues.DEF_INTERPOLANTS);
//		preferences.setDefault(PreferenceValues.NAME_EDGES2TRUE, PreferenceValues.DEF_EDGES2TRUE);
//		preferences.setDefault(PreferenceValues.NAME_ADDITIONAL_EDGES, PreferenceValues.DEF_ADDITIONAL_EDGES);
//		preferences.setDefault(PreferenceValues.NAME_DUMPFORMULAS, PreferenceValues.DEF_DUMPFORMULAS);
//		preferences.setDefault(PreferenceValues.NAME_DUMPAUTOMATA, PreferenceValues.DEF_DUMPAUTOMATA);		
//		preferences.setDefault(PreferenceValues.NAME_DUMPPATH, PreferenceValues.DEF_DUMPPATH);
//		preferences.setDefault(PreferenceValues.NAME_DETERMINIZATION, PreferenceValues.DEF_DETERMINIZATION);
//		preferences.setDefault(PreferenceValues.NAME_DIFFERENCE, PreferenceValues.DEF_DIFFERENCE);
//		preferences.setDefault(PreferenceValues.NAME_DETERMINIZATION, PreferenceValues.DEF_DETERMINIZATION);
//		preferences.setDefault(PreferenceValues.NAME_MINIMIZE, PreferenceValues.DEF_MINIMIZE);
//		preferences.setDefault(PreferenceValues.NAME_CONCURRENCY, PreferenceValues.DEF_CONCURRENCY);
		
	}

	
	public void init(IWorkbench workbench) {}

	
	public boolean performOk() {
		try{
			preferences.save();
		}catch(IOException ioe){
			logger.warn(ioe);
		}
		return super.performOk();
	}
	
}