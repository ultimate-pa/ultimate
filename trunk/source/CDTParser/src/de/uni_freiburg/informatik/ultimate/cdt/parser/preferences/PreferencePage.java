package de.uni_freiburg.informatik.ultimate.cdt.parser.preferences;

import java.io.IOException;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.PathEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.cdt.parser.Activator;

/**
 * On this preference page the user has the availability to specify the
 * include-paths, which are needed to resolve all includes in the given C-File.
 * 
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 11.03.2012
 */
public class PreferencePage extends FieldEditorPreferencePage implements
		IWorkbenchPreferencePage {

	/**
	 * Logger instance.
	 */
	public static final Logger logger = Logger.getLogger(PreferencePage.class);
	/**
	 * The name for the given FieldEditor, which we use to specify the inlcude
	 * paths.
	 */
	public static final String INCLUDE_PATHS = "Include-Paths";
	/**
	 * The label which describes the FieldEditor.
	 */
	public static final String INCLUDE_PATHS_DESC = "Please specify the "
			+ "include paths, to parse the given C-File:";
	/**
	 * The label which is shown in the folder chooser.
	 */
	public static final String INCLUDE_PATHS_CHOOSER = "Please choose a folder:";

	/**
	 * Holds the preference object.
	 */
	private final ScopedPreferenceStore preferences;

	/**
	 * Constructor calling super constructor and initializing preferences.
	 */
	public PreferencePage() {
		super(GRID);
		preferences = new ScopedPreferenceStore(InstanceScope.INSTANCE,
				Activator.PLUGIN_ID);
		setPreferenceStore(preferences);
	}

	@Override
	protected void createFieldEditors() {
		PathEditor paths = new PathEditor(INCLUDE_PATHS, INCLUDE_PATHS_DESC,
				INCLUDE_PATHS_CHOOSER, getFieldEditorParent());
		addField(paths);
	}

	@Override
	public void init(IWorkbench workbench) {
		// unused.
	}

	@Override
	public boolean performOk() {
		try {
			preferences.save();
		} catch (IOException ioe) {
			logger.warn(ioe);
		}
		return super.performOk();
	}
}
