package de.uni_freiburg.informatik.ultimate.LTL2aut.preferences;

import java.io.IOException;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.LTL2aut.Activator;

public class PreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
	
	public static final Logger logger =  Logger.getLogger(PreferencePage.class);	
	private final ScopedPreferenceStore preferences;
	
	public static String TOOLLOCATION = "C:\\ltl2ba.exe";
	public static String COMMANDLINEARGUMENT = " -f \\\" $1 \\\"";

	public PreferencePage(){
		super(GRID);
		preferences = new ScopedPreferenceStore(ConfigurationScope.INSTANCE, Activator.PLUGIN_ID);
		setPreferenceStore(preferences);
	}
	
	@Override
	protected void createFieldEditors() {	
		FileFieldEditor toolPath = new FileFieldEditor(
				TOOLLOCATION,
				"Path to ltl->ba tool (LTL2BA, LTL3BA) :",
				getFieldEditorParent());
		addField(toolPath);
		
		StringFieldEditor toolArguments = new StringFieldEditor(
				COMMANDLINEARGUMENT,
				"Command line string:",
				getFieldEditorParent()
				);
		addField(toolArguments);
	}
	
	public boolean performOk() {
			try {
				preferences.save();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		return super.performOk();
	}
	
	public void init(IWorkbench workbench) {
		setDescription("Set the properties for the LTLxBA tool to wrap by this plugin.\n"
				+ "-Tools known to work with the wrapper are LTL2BA, LTL3BA\n"
				+ "-As commandline string working with both tools: '-f \" $1 \"' "
				+ "(use #1 as placeholder for the LTL formula)\n");
		
	}

}
