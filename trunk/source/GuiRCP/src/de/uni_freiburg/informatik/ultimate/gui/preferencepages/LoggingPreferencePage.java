package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.constants.PreferenceConstants;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

public class LoggingPreferencePage extends FieldEditorPreferencePage implements
		IWorkbenchPreferencePage {

	private ScopedPreferenceStore preferenceStore;
	private StringFieldEditor root;
	private StringFieldEditor core;
	private StringFieldEditor controller;
	private StringFieldEditor tools;
	private StringFieldEditor modif;

	public LoggingPreferencePage() {
		super(GRID);

		// init default values
		preferenceStore = new ScopedPreferenceStore(new InstanceScope(),
				Activator.s_PLUGIN_ID);
		setPreferenceStore(preferenceStore);
		preferenceStore.setDefault(PreferenceConstants.PREFID_ROOT,
				PreferenceConstants.VALUE_DEFAULT_LOGGING_PREF);
		preferenceStore.setDefault(PreferenceConstants.PREFID_CORE,
				PreferenceConstants.VALUE_DEFAULT_LOGGING_PREF);
		preferenceStore.setDefault(PreferenceConstants.PREFID_TOOLS,
				PreferenceConstants.VALUE_DEFAULT_LOGGING_PREF);
		preferenceStore.setDefault(PreferenceConstants.PREFID_CONTROLLER,
				PreferenceConstants.VALUE_DEFAULT_LOGGING_PREF);
		preferenceStore.setDefault(PreferenceConstants.PREFID_PLUGINS,
				PreferenceConstants.VALUE_DEFAULT_LOGGING_PREF);
		preferenceStore.setDefault(PreferenceConstants.PREFID_DETAILS, "");

		// set description
		setDescription(PreferenceConstants.LOGGING_PREFERENCES_DESC);
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
		root = new StringFieldEditor(PreferenceConstants.PREFID_ROOT,
				PreferenceConstants.LABEL_ROOT_PREF, getFieldEditorParent());
		addField(root);
		core = new StringFieldEditor(PreferenceConstants.PREFID_CORE,
				PreferenceConstants.LABEL_CORE_PREF, getFieldEditorParent());
		addField(core);
		controller = new StringFieldEditor(PreferenceConstants.PREFID_CONTROLLER,
				PreferenceConstants.LABEL_CONTROLLER_PREF, getFieldEditorParent());
		addField(controller);
		modif = new StringFieldEditor(PreferenceConstants.PREFID_PLUGINS,
				PreferenceConstants.LABEL_PLUGINS_PREF,
				getFieldEditorParent());
		addField(modif);
		tools = new StringFieldEditor(PreferenceConstants.PREFID_TOOLS,
				PreferenceConstants.LABEL_TOOLS_PREF, getFieldEditorParent());
		addField(tools);

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.preference.FieldEditorPreferencePage#checkState()
	 */
	@Override
	protected void checkState() {
		super.checkState();
		if (isValid())
			checkLogLevelState(root);
		if (isValid())
			checkLogLevelState(core);
		if (isValid())
			checkLogLevelState(controller);
		if (isValid())
			checkLogLevelState(modif);
		if (isValid())
			checkLogLevelState(tools);
	}

	/**
	 * void checkLogLevelState
	 * 
	 * @param field
	 */
	private void checkLogLevelState(StringFieldEditor field) {
		if (field.getStringValue() == null || field.getStringValue().isEmpty()) {
			setErrorMessage(null);
			setValid(true);
		} else if (isLogLevel(field.getStringValue())) {
			setErrorMessage(null);
			setValid(true);
		} else {
			setErrorMessage(PreferenceConstants.INVALID_LOGLEVEL);
			setValid(false);
		}

	}

	/**
	 * boolean isLogLevel
	 * 
	 * @param s
	 * @return <code>true</code> if and only if the value represents a valid
	 * 			log level.
	 */
	private boolean isLogLevel(String s) {
		return s.toUpperCase().equals(
				PreferenceConstants.VALUE_TRACE_LOGGING_PREF)
				|| s.toUpperCase().equals(
						PreferenceConstants.VALUE_DEBUG_LOGGING_PREF)
				|| s.toUpperCase().equals(
						PreferenceConstants.VALUE_INFO_LOGGING_PREF)
				|| s.toUpperCase().equals(
						PreferenceConstants.VALUE_WARN_LOGGING_PREF)
				|| s.toUpperCase().equals(
						PreferenceConstants.VALUE_ERROR_LOGGING_PREF)
				|| s.toUpperCase().equals(
						PreferenceConstants.VALUE_FATAL_LOGGING_PREF);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.jface.preference.FieldEditorPreferencePage#propertyChange
	 * (org.eclipse.jface.util.PropertyChangeEvent)
	 */
	@Override
	public void propertyChange(PropertyChangeEvent event) {
		super.propertyChange(event);
		if (event.getProperty().equals(FieldEditor.VALUE)) {
			checkState();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	@Override
	public void init(IWorkbench workbench) {

	}

}