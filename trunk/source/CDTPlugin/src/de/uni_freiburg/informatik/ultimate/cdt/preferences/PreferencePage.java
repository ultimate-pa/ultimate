/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.preferences;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.cdt.Activator;
import de.uni_freiburg.informatik.ultimate.gui.preferencepages.UltimatePreferencePageFactory;

/**
 * This is should be the main category for all Ultimate configurations. Here we
 * configure which Tool-Chain is used, we decouple this from Codan, because
 * there is no real access to get their preferences.
 * 
 * @author Stefan Wissert
 * 
 */
public class PreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {

	public static String TOOLCHAIN_SELECTION_TEXT = "ToolchainSelection";

	public static String TOOLCHAIN_SELECTION_LABEL = "Please select your Toolchain: ";

	/**
	 * Holds the preference object.
	 */
	private final ScopedPreferenceStore preferences;

	/**
	 * Constructor calling super constructor and initializing preferences.
	 */
	public PreferencePage() {
		super(GRID);
		preferences = new ScopedPreferenceStore(InstanceScope.INSTANCE, Activator.PLUGIN_ID);
		setPreferenceStore(preferences);
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
		// we want to choose the toolchains which we use!
		// we read out the Directory "Toolchains", and create prefs
		File toolchainDir = null;
		URL url = FileLocator.find(Platform.getBundle(Activator.PLUGIN_ID), new Path("toolchains"), null);
		try {
			URI uri = new URI(FileLocator.toFileURL(url).toString().replace(" ", "%20"));
			toolchainDir = new File(uri);
		} catch (IOException e2) {
			e2.printStackTrace();
		} catch (URISyntaxException e) {
			e.printStackTrace();
		}

		ArrayList<String[]> comboValues = new ArrayList<String[]>();
		// Iterate over all Files in the Directory
		for (File f : toolchainDir.listFiles()) {
			String[] params = f.getName().split("\\.");
			String tName = params[0];
			if (tName.equals("") || params.length < 2 || !params[1].equals("xml")) {
				continue;
			}
			comboValues.add(new String[] { tName, tName });
		}

		ComboFieldEditor toolchainSelection = new ComboFieldEditor(TOOLCHAIN_SELECTION_TEXT, TOOLCHAIN_SELECTION_LABEL,
				comboValues.toArray(new String[comboValues.size()][2]), getFieldEditorParent());

		addField(toolchainSelection);
	}

	@Override
	public void init(IWorkbench workbench) {
		
	}

	@Override
	public boolean performOk() {
		try {
			preferences.save();
		} catch (IOException ioe) {
			System.out.println(ioe);
		}
		return super.performOk();
	}

}
