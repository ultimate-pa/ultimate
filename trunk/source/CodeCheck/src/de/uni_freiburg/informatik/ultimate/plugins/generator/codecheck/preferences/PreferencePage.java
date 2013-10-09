package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences;


import java.io.IOException;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.PreferencePage;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.PreferenceValues;

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
		
		BooleanFieldEditor onlyMainProcedure = new BooleanFieldEditor(
				PreferenceValues.NAME_ONLYMAINPROCEDURE,
				PreferenceValues.LABEL_ONLYMAINPROCEDURE,
				getFieldEditorParent());
		addField(onlyMainProcedure);	
		
		BooleanFieldEditor memoizeNormalEdgeChecks = new BooleanFieldEditor(
				PreferenceValues.NAME_MEMOIZENORMALEDGECHECKS,
				PreferenceValues.LABEL_MEMOIZENORMALEDGECHECKS,
				getFieldEditorParent());
		addField(memoizeNormalEdgeChecks);
		
		BooleanFieldEditor memoizeReturnEdgeChecks = new BooleanFieldEditor(
				PreferenceValues.NAME_MEMOIZERETURNEDGECHECKS,
				PreferenceValues.LABEL_MEMOIZERETURNEDGECHECKS,
				getFieldEditorParent());
		addField(memoizeReturnEdgeChecks);
		
		ComboFieldEditor solverandinterpolator = new ComboFieldEditor(
		PreferenceValues.NAME_SOLVERANDINTERPOLATOR, 
		PreferenceValues.LABEL_SOLVERANDINTERPOLATOR,
		new String[][]{{PreferenceValues.VALUE_SOLVERANDINTERPOLATOR_SMTINTERPOL.toString(), 
			PreferenceValues.VALUE_SOLVERANDINTERPOLATOR_SMTINTERPOL.toString()},
				{PreferenceValues.VALUE_SOLVERANDINTERPOLATOR_Z3SPWP.toString(), 
				PreferenceValues.VALUE_SOLVERANDINTERPOLATOR_Z3SPWP.toString()}},
		getFieldEditorParent());
		addField(solverandinterpolator);	
		
		ComboFieldEditor predicateUnification = new ComboFieldEditor(
		PreferenceValues.NAME_PREDICATEUNIFICATION, 
		PreferenceValues.LABEL_PREDICATEUNIFICATION,
		new String[][]{{PreferenceValues.VALUE_PREDICATEUNIFICATION_PERVERIFICATION.toString(), 
			PreferenceValues.VALUE_PREDICATEUNIFICATION_PERVERIFICATION.toString()},
				{PreferenceValues.VALUE_PREDICATEUNIFICATION_PERITERATION.toString(), 
				PreferenceValues.VALUE_PREDICATEUNIFICATION_PERITERATION.toString()},
						{PreferenceValues.VALUE_PREDICATEUNIFICATION_NONE.toString(), 
				PreferenceValues.VALUE_PREDICATEUNIFICATION_NONE.toString()}},
		getFieldEditorParent());
		addField(predicateUnification);	
		
		StringFieldEditor graphWriterPath = new StringFieldEditor(
				PreferenceValues.NAME_GRAPHWRITERPATH,
				PreferenceValues.LABEL_GRAPHWRITERPATH,
				getFieldEditorParent());
		graphWriterPath.setEmptyStringAllowed(true);
		graphWriterPath.setTextLimit(40);
		addField(graphWriterPath);
	
		
		IntegerFieldEditor timeout = new IntegerFieldEditor(
				PreferenceValues.NAME_TIMEOUT, 
				PreferenceValues.LABEL_TIMEOUT,	
				getFieldEditorParent(), 
				6);
		timeout.setValidRange(0, 1000000);
		addField(timeout);
		
//		IntegerFieldEditor iterations = new IntegerFieldEditor(
//				PreferenceValues.NAME_ITERATIONS, 
//				PreferenceValues.LABEL_ITERATIONS,	
//				getFieldEditorParent(), 
//				6);
//		iterations.setValidRange(0, 1000000);
//		addField(iterations);
//

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