/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences;

import java.io.IOException;

import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.logging.UltimateLoggerFactory;

/**
 * The preference page to set up the creation of a log file for Ultimate Output.
 * After set up the preferences, Ultimate may be has to be restarted, because
 * the Logger is set up during the start up process. <br>
 * The basic preferences are:
 * <ul>
 * <li>Check Box for general activation</li>
 * <li>Directory, where to store it</li>
 * <li>Name of the Log-File</li>
 * </ul>
 * 
 * @author Stefan Wissert
 * 
 */
public class LogFilePreferencePage extends FieldEditorPreferencePage implements
		IWorkbenchPreferencePage {

	/**
	 * Holds the preference object.
	 */
	private final ScopedPreferenceStore preferences;

	public static final String DEFAULT_LOGFILE = "UltimateLogOutput";

	public static final String DEFAULT_LOGFILE_DIR = Platform
			.getInstanceLocation().getURL().getPath();

	public LogFilePreferencePage() {
		super(GRID);
		preferences = new ScopedPreferenceStore(InstanceScope.INSTANCE,
				Activator.s_PLUGIN_ID);
		setPreferenceStore(preferences);
		this.setDescription(IPreferenceConstants.DESC_LOGFILE);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.preference.FieldEditorPreferencePage#createFieldEditors
	 * ()
	 */
	@Override
	protected void createFieldEditors() {
		// Basic check-box for enabling the logging into a file
		BooleanFieldEditor logFile = new BooleanFieldEditor(
				IPreferenceConstants.PREFID_LOGFILE,
				IPreferenceConstants.LABEL_LOGFILE, getFieldEditorParent());
		addField(logFile);

		// the name of the log file
		StringFieldEditor nameLogFile = new StringFieldEditor(
				IPreferenceConstants.PREFID_LOGFILE_NAME,
				IPreferenceConstants.LABEL_LOGFILE_NAME, getFieldEditorParent());
		addField(nameLogFile);
		preferences.setDefault(IPreferenceConstants.PREFID_LOGFILE_NAME,
				DEFAULT_LOGFILE);
		// the directory of the log file
		DirectoryFieldEditor dirLogFile = new DirectoryFieldEditor(
				IPreferenceConstants.PREFID_LOGFILE_DIR,
				IPreferenceConstants.LABEL_LOGFILE_DIR, getFieldEditorParent());
		addField(dirLogFile);
		preferences.setDefault(IPreferenceConstants.PREFID_LOGFILE_DIR,
				DEFAULT_LOGFILE_DIR);
	}

	@Override
	public void init(IWorkbench workbench) {
	}

	@Override
	public boolean performOk() {
		try {
			preferences.save();
		} catch (IOException ioe) {
			System.err.println("Failed saving preferences for log file");
		}
		boolean val = super.performOk();
		UltimateLoggerFactory.getInstance().appendLogFile();
		return val;
	}

}
