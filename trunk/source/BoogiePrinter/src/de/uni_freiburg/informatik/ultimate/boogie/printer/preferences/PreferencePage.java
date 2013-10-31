/**
 * Eclipse RCP Preference Page for Boogie Printer.
 */
package de.uni_freiburg.informatik.ultimate.boogie.printer.preferences;

import java.io.IOException;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.boogie.printer.Activator;

/**
 * On this preference page the user has the possibility to specify the path,
 * where to dump the Boogie file.
 * 
 * @author Markus Lindenmann
 * @date 22.04.2012
 */
public class PreferencePage extends FieldEditorPreferencePage implements
		IWorkbenchPreferencePage {

	/**
	 * Logger instance.
	 */
	private static final Logger logger = Logger.getLogger(PreferencePage.class);
	/**
	 * Holds the preference object.
	 */
	private final ScopedPreferenceStore preferences;

	private BooleanFieldEditor mSaveInSourceFolderEditor;
	private static final String SAVE_IN_SOURCE_DIRECTORY_NAME = "SaveInSource";
	private static final String SAVE_IN_SOURCE_DIRECTORY_LABEL = "Save file in source directory?";
	private static final boolean SAVE_IN_SOURCE_DIRECTORY_DEFAULT = false;

	private BooleanFieldEditor mUniqueNameEditor;
	private static final String UNIQUE_NAME_NAME = "UniqueName";
	private static final String UNIQUE_NAME_LABEL = "Use automatic naming?";
	private static final boolean UNIQUE_NAME_DEFAULT = false;

	private DirectoryFieldEditor mDumpPathEditor;
	private static final String DUMP_PATH_NAME = "Dump-Path";
	private static final String DUMP_PATH_LABEL = "Dump path:";
	private static final String DUMP_PATH_DEFAULT = System
			.getProperty("java.io.tmpdir");

	private StringFieldEditor mFilenameEditor;
	private static final String FILE_NAME_NAME = "File-Name";
	private static final String FILE_NAME_LABEL = "File name:";
	private static final String FILE_NAME_DEFAULT = "boogiePrinter.bpl";

	/**
	 * Constructor calling super constructor and initializing preferences.
	 */
	public PreferencePage() {
		super(GRID);
		preferences = new ScopedPreferenceStore(InstanceScope.INSTANCE,
				Activator.s_PLUGIN_ID);
		setPreferenceStore(preferences);
	}

	@Override
	protected void createFieldEditors() {
		IPreferenceStore store = Activator.getDefault().getPreferenceStore();
		mDumpPathEditor = new DirectoryFieldEditor(DUMP_PATH_NAME,
				DUMP_PATH_LABEL, getFieldEditorParent());
		mDumpPathEditor.setEmptyStringAllowed(false);
		store.setDefault(DUMP_PATH_NAME, DUMP_PATH_DEFAULT);

		mFilenameEditor = new StringFieldEditor(FILE_NAME_NAME,
				FILE_NAME_LABEL, getFieldEditorParent());
		mFilenameEditor.setEmptyStringAllowed(false);
		mFilenameEditor.setTextLimit(40);
		store.setDefault(FILE_NAME_NAME, FILE_NAME_DEFAULT);

		mSaveInSourceFolderEditor = new BooleanFieldEditor(
				SAVE_IN_SOURCE_DIRECTORY_NAME, SAVE_IN_SOURCE_DIRECTORY_LABEL,
				getFieldEditorParent()) {
			@Override
			protected void fireValueChanged(String property, Object oldValue,
					Object newValue) {
				super.fireValueChanged(property, oldValue, newValue);
				if ((Boolean) newValue) {
					mDumpPathEditor.setEnabled(false, getFieldEditorParent());
				} else {
					mDumpPathEditor.setEnabled(true, getFieldEditorParent());
				}
			}
		};

		store.setDefault(SAVE_IN_SOURCE_DIRECTORY_NAME,
				SAVE_IN_SOURCE_DIRECTORY_DEFAULT);

		mUniqueNameEditor = new BooleanFieldEditor(UNIQUE_NAME_NAME,
				UNIQUE_NAME_LABEL, getFieldEditorParent()) {
			@Override
			protected void fireValueChanged(String property, Object oldValue,
					Object newValue) {
				super.fireValueChanged(property, oldValue, newValue);
				if ((Boolean) newValue) {
					mFilenameEditor.setEnabled(false, getFieldEditorParent());
				} else {
					mFilenameEditor.setEnabled(true, getFieldEditorParent());
				}
			}
		};

		store.setDefault(UNIQUE_NAME_NAME, UNIQUE_NAME_DEFAULT);

		addField(mDumpPathEditor);
		addField(mFilenameEditor);
		addField(mSaveInSourceFolderEditor);
		addField(mUniqueNameEditor);

	}

	@Override
	protected void initialize() {
		super.initialize();
		if (mSaveInSourceFolderEditor.getBooleanValue()) {
			mDumpPathEditor.setEnabled(false, getFieldEditorParent());
		} else {
			mDumpPathEditor.setEnabled(true, getFieldEditorParent());
		}

		if (mUniqueNameEditor.getBooleanValue()) {
			mFilenameEditor.setEnabled(false, getFieldEditorParent());
		} else {
			mFilenameEditor.setEnabled(true, getFieldEditorParent());
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.preference.FieldEditorPreferencePage#performOk()
	 */
	@Override
	public boolean performOk() {
		try {
			preferences.save();
		} catch (IOException ioe) {
			logger.warn(ioe);
		}
		return super.performOk();
	}

	@Override
	public void init(IWorkbench workbench) {
		// does nothing on purpose
	}

	public static String getDumpPath() {
		return InstanceScope.INSTANCE.getNode(Activator.s_PLUGIN_ID).get(
				DUMP_PATH_NAME, DUMP_PATH_DEFAULT);
	}

	public static String getFilename() {
		return InstanceScope.INSTANCE.getNode(Activator.s_PLUGIN_ID).get(
				FILE_NAME_NAME, FILE_NAME_DEFAULT);
	}

	public static boolean getUseUniqueFilename() {
		return InstanceScope.INSTANCE.getNode(Activator.s_PLUGIN_ID)
				.getBoolean(UNIQUE_NAME_NAME, UNIQUE_NAME_DEFAULT);
	}

	public static boolean getSaveInSourceDirectory() {
		return InstanceScope.INSTANCE.getNode(Activator.s_PLUGIN_ID)
				.getBoolean(SAVE_IN_SOURCE_DIRECTORY_NAME,
						SAVE_IN_SOURCE_DIRECTORY_DEFAULT);
	}
}
