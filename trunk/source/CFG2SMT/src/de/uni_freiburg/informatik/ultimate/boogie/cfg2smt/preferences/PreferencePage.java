package de.uni_freiburg.informatik.ultimate.boogie.cfg2smt.preferences;

import java.io.IOException;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.boogie.cfg2smt.Activator;

public class PreferencePage extends FieldEditorPreferencePage
implements IWorkbenchPreferencePage {

	public static final Logger logger =  Logger.getLogger(PreferencePage.class);
	
	private final ScopedPreferenceStore preferences;

	public PreferencePage(){
		super(GRID);
		preferences = new ScopedPreferenceStore(ConfigurationScope.INSTANCE, Activator.PLUGIN_ID);
		setPreferenceStore(preferences);
	}
	
	@Override
	protected void createFieldEditors() {
//		String[][] entryNamesAndValues = new String [6][2];
//		entryNamesAndValues[0][0] = "SOLVER_SMTLIB";
//		entryNamesAndValues[0][1] = "0";
//		entryNamesAndValues[1][0] = "SOLVER_SMTINTERPOL";
//		entryNamesAndValues[1][1] = "1";
//		entryNamesAndValues[2][0] = "SOLVER_Z3_SIMPLIFY";
//		entryNamesAndValues[2][1] = "2";
//		entryNamesAndValues[3][0] = "SOLVER_Z3_NATIVE";
//		entryNamesAndValues[3][1] = "3";
//		entryNamesAndValues[4][0] = "SOLVER_Z3_NATIVE_INTERPOL";
//		entryNamesAndValues[4][1] = "4";
//		entryNamesAndValues[5][0] = "SOLVER_GROUNDIFY";
//		entryNamesAndValues[5][1] = "5";
//		
//		ComboFieldEditor selectedSolver = new ComboFieldEditor(PreferenceValues.NAME_SELECTEDSOLVER,
//				PreferenceValues.LABEL_SELECTEDSOLVER, entryNamesAndValues, getFieldEditorParent());
//		addField(selectedSolver);
//		
		DirectoryFieldEditor dumpPath = new DirectoryFieldEditor(PreferenceValues.NAME_DUMPPATH, PreferenceValues.LABEL_DUMPPATH,
				getFieldEditorParent());
		addField(dumpPath);
	}
	
	public boolean performOk() {
		try{
			preferences.save();
		}catch(IOException ioe){
			logger.warn(ioe);
		}
		return super.performOk();
	}
	
	@Override
	public void init(IWorkbench workbench) {
		// TODO Auto-generated method stub
		
	}
}
