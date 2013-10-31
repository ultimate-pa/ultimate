/**
 * Eclipse RCP Preference Page for CACSL to Boogie Translator.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences;

import java.io.IOException;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.TranslationMode;

/**
 * On this preference page the user has the possibility to specify the
 * translation mode.
 * 
 * @author Markus Lindenmann
 * @date 12.06.2012
 */
public class PreferencePage extends FieldEditorPreferencePage implements
        IWorkbenchPreferencePage {

    /**
     * Logger instance.
     */
    public static final Logger logger = Logger.getLogger(PreferencePage.class);
    /**
     * Holds the preference object.
     */
    private final ScopedPreferenceStore preferences;
    /**
     * The name for the mode setting.
     */
    public static final String NAME_MODE = "Translation-Mode";
    /**
     * The label which describes the mode setting.
     */
    public static final String LABEL_MODE = "Translation Mode:";
    /**
     * The name for the checkedMethod setting.
     */
    public static String NAME_MAINPROC = "CheckedMethod";
    /**
     * The label which describes the checedMethod setting.
     */
    public static final String LABEL_MAINPROC = "Checked method. Library mode if empty.";

    public static final String NAME_CHECK_POINTER_VALIDITY = "CheckPointerValidity";
    public static final String LABEL_CHECK_POINTER_VALIDITY = "Check if pointer is valid before each access";
    

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
    public void init(IWorkbench workbench) {
        // unused.
    }

    @Override
    protected void createFieldEditors() {
        IPreferenceStore store = Activator.getDefault().getPreferenceStore();
        store.setDefault(NAME_MODE, TranslationMode.BASE.toString());

        String[][] vals = new String[TranslationMode.values().length][];
        for (int i = 0; i < TranslationMode.values().length; i++) {
            TranslationMode m = TranslationMode.values()[i];
            vals[i] = new String[] { m.toDescString(), m.toString() };
        }
        RadioGroupFieldEditor mode = new RadioGroupFieldEditor(NAME_MODE,
                LABEL_MODE, 1, vals, getFieldEditorParent());
        mode.loadDefault();
        addField(mode);

        StringFieldEditor checkedMethod = new StringFieldEditor(NAME_MAINPROC,
                LABEL_MAINPROC, getFieldEditorParent());
        checkedMethod.setEmptyStringAllowed(true);
        checkedMethod.setTextLimit(40);
        addField(checkedMethod);
        
		BooleanFieldEditor checkPointerValidity = new BooleanFieldEditor(
				NAME_CHECK_POINTER_VALIDITY,
				LABEL_CHECK_POINTER_VALIDITY,
				getFieldEditorParent());
		addField(checkPointerValidity);
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
