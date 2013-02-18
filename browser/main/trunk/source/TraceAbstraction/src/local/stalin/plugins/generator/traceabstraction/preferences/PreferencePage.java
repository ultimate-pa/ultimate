package local.stalin.plugins.generator.traceabstraction.preferences;


import java.io.IOException;

import local.stalin.plugins.generator.traceabstraction.Activator;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

/**
 * this calls contributes to the extensionpoint:
 * org.eclipse.ui.prefgerencePages   see at the plugin.xml
 * 
 */
public class PreferencePage extends FieldEditorPreferencePage
		implements IWorkbenchPreferencePage {

	public static final Logger logger =  Logger.getLogger(PreferencePage.class);
	
	
	private static final ScopedPreferenceStore preferences = new ScopedPreferenceStore(new ConfigurationScope(),Activator.s_PLUGIN_ID);

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
		
		ComboFieldEditor solver = new ComboFieldEditor(
				PreferenceValues.NAME_SOLVER,
				PreferenceValues.LABEL_SOLVER,
				new String[][]{{PreferenceValues.VALUE_SOLVER_SMTINTERPOL, PreferenceValues.VALUE_SOLVER_SMTINTERPOL},
						{PreferenceValues.VALUE_SOLVER_GROUNDIFY, PreferenceValues.VALUE_SOLVER_GROUNDIFY}},
				getFieldEditorParent());
		addField(solver);	
				
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

		ComboFieldEditor interpolants = new ComboFieldEditor(
				PreferenceValues.NAME_INTERPOLATED_LOCS,
				PreferenceValues.LABEL_INTERPOLATED_LOCS, 
				new String[][]{{PreferenceValues.VALUE_CUTPOINTS, PreferenceValues.VALUE_CUTPOINTS},
						{PreferenceValues.VALUE_ALL_LOC, PreferenceValues.VALUE_ALL_LOC}},
				getFieldEditorParent());
		addField(interpolants);
		
		BooleanFieldEditor edges2True = new BooleanFieldEditor(
				PreferenceValues.NAME_EDGES2TRUE,
				PreferenceValues.LABEL_EDGES2TRUE,
				getFieldEditorParent());
		addField(edges2True); 

		ComboFieldEditor additionalEdges = new ComboFieldEditor(
				PreferenceValues.NAME_ADDITIONAL_EDGES,
				PreferenceValues.LABEL_ADDITIONAL_EDGES, 
				new String[][]{{PreferenceValues.VALUE_NO_EDGE, PreferenceValues.VALUE_NO_EDGE},
						{PreferenceValues.VALUE_CANONICAL, PreferenceValues.VALUE_CANONICAL},
						{PreferenceValues.VALUE_EAGER, PreferenceValues.VALUE_EAGER}},
				getFieldEditorParent());
		addField(additionalEdges);

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
						{PreferenceValues.VALUE_SELFLOOP, PreferenceValues.VALUE_SELFLOOP}},
				getFieldEditorParent());
		addField(determinization);
		
		BooleanFieldEditor difference = new BooleanFieldEditor(
				PreferenceValues.NAME_DIFFERENCE,
				PreferenceValues.LABEL_DIFFERENCE,
				getFieldEditorParent());
		addField(difference);
		
		BooleanFieldEditor minimize = new BooleanFieldEditor(
				PreferenceValues.NAME_MINIMIZE,
				PreferenceValues.LABEL_MINIMIZE,
				getFieldEditorParent());
		addField(minimize);
	
		preferences.setDefault(PreferenceValues.NAME_INTERPROCEDUTAL, PreferenceValues.DEF_INTERPROCEDUTAL);
		preferences.setDefault(PreferenceValues.NAME_SOLVER, PreferenceValues.DEF_SOLVER);
		preferences.setDefault(PreferenceValues.NAME_ITERATIONS, PreferenceValues.DEF_ITERATIONS);
		preferences.setDefault(PreferenceValues.NAME_ARTIFACT, PreferenceValues.DEF_ARTIFACT);
		preferences.setDefault(PreferenceValues.NAME_WATCHITERATION, PreferenceValues.DEF_WATCHITERATION);
		preferences.setDefault(PreferenceValues.NAME_INTERPOLATED_LOCS, PreferenceValues.DEF_INTERPOLANTS);
		preferences.setDefault(PreferenceValues.NAME_EDGES2TRUE, PreferenceValues.DEF_EDGES2TRUE);
		preferences.setDefault(PreferenceValues.NAME_ADDITIONAL_EDGES, PreferenceValues.DEF_ADDITIONAL_EDGES);
		preferences.setDefault(PreferenceValues.NAME_DUMPFORMULAS, PreferenceValues.DEF_DUMPFORMULAS);
		preferences.setDefault(PreferenceValues.NAME_DUMPAUTOMATA, PreferenceValues.DEF_DUMPAUTOMATA);		
		preferences.setDefault(PreferenceValues.NAME_DUMPPATH, PreferenceValues.DEF_DUMPPATH);
		preferences.setDefault(PreferenceValues.NAME_DETERMINIZATION, PreferenceValues.DEF_DETERMINIZATION);
		preferences.setDefault(PreferenceValues.NAME_DIFFERENCE, PreferenceValues.DEF_DIFFERENCE);
		preferences.setDefault(PreferenceValues.NAME_DETERMINIZATION, PreferenceValues.DEF_DETERMINIZATION);
		preferences.setDefault(PreferenceValues.NAME_MINIMIZE, PreferenceValues.DEF_MINIMIZE);
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