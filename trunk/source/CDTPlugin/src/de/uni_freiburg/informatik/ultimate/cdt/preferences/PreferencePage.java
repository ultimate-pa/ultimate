/*
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CDTPlugin plug-in.
 * 
 * The ULTIMATE CDTPlugin plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CDTPlugin plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTPlugin plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTPlugin plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CDTPlugin plug-in grant you additional permission
 * to convey the resulting work.
 */
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

/**
 * This is should be the main category for all Ultimate configurations. Here we
 * configure which Tool-Chain is used, we decouple this from Codan, because
 * there is no real access to get their preferences.
 * 
 * @author Stefan Wissert
 * 
 */
public class PreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {

	public static final String TOOLCHAIN_SELECTION_TEXT = "ToolchainSelection";

	public static final String TOOLCHAIN_SELECTION_LABEL = "Please select your Toolchain: ";

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
		final URL url = FileLocator.find(Platform.getBundle(Activator.PLUGIN_ID), new Path("toolchains"), null);
		try {
			final URI uri = new URI(FileLocator.toFileURL(url).toString().replace(" ", "%20"));
			toolchainDir = new File(uri);
		} catch (final IOException e2) {
			e2.printStackTrace();
		} catch (final URISyntaxException e) {
			e.printStackTrace();
		}

		final ArrayList<String[]> comboValues = new ArrayList<String[]>();
		// Iterate over all Files in the Directory
		for (final File f : toolchainDir.listFiles()) {
			final String[] params = f.getName().split("\\.");
			final String tName = params[0];
			if (tName.equals("") || params.length < 2 || !params[1].equals("xml")) {
				continue;
			}
			comboValues.add(new String[] { tName, tName });
		}

		final ComboFieldEditor toolchainSelection = new ComboFieldEditor(TOOLCHAIN_SELECTION_TEXT, TOOLCHAIN_SELECTION_LABEL,
				comboValues.toArray(new String[comboValues.size()][2]), getFieldEditorParent());

		addField(toolchainSelection);
	}

	@Override
	public void init(final IWorkbench workbench) {
		
	}

	@Override
	public boolean performOk() {
		try {
			preferences.save();
		} catch (final IOException ioe) {
			System.out.println(ioe);
		}
		return super.performOk();
	}

}
