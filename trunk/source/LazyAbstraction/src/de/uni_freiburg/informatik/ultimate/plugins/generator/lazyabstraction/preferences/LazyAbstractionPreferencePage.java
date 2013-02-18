package de.uni_freiburg.informatik.ultimate.plugins.generator.lazyabstraction.preferences;

import org.eclipse.jface.preference.*;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.IWorkbench;
import de.uni_freiburg.informatik.ultimate.plugins.generator.lazyabstraction.Activator;

/**
 * This class represents a preference page that
 * is contributed to the Preferences dialog. By 
 * subclassing <samp>FieldEditorPreferencePage</samp>, we
 * can use the field support built into JFace that allows
 * us to create a page that is small and knows how to 
 * save, restore and apply itself.
 * <p>
 * This page is used to modify preferences only. They
 * are stored in the preference store that belongs to
 * the main plug-in class. That way, preferences can
 * be accessed directly via the preference store.
 */

public class LazyAbstractionPreferencePage
	extends FieldEditorPreferencePage
	implements IWorkbenchPreferencePage {

	public LazyAbstractionPreferencePage() {
		super(GRID);
		setPreferenceStore(Activator.getDefault().getPreferenceStore());
		setDescription("Preference page for the Lazy Abstraction (McMillan) plugin");
	}
	
	/**
	 * Creates the field editors. Field editors are abstractions of
	 * the common GUI blocks needed to manipulate various types
	 * of preferences. Each field editor knows how to save and
	 * restore itself.
	 */
	public void createFieldEditors() {
		addField(
				new BooleanFieldEditor(
					PreferenceConstants.P_MEMOIZE,
					"&Memoize formulas of implication checks",
					getFieldEditorParent()));
		addField(new DirectoryFieldEditor(PreferenceConstants.P_IMAGE_PATH, 
				"&Path for graph output (empty for no output):", getFieldEditorParent()));
		addField(
				new BooleanFieldEditor(
					PreferenceConstants.P_ANNOTATE_EDGES,
					"&Show formulas of edges",
					getFieldEditorParent()));
		addField(
				new BooleanFieldEditor(
					PreferenceConstants.P_ANNOTATE_NODES,
					"&Show formulas of nodes",
					getFieldEditorParent()));
		addField(
				new BooleanFieldEditor(
					PreferenceConstants.P_SHOW_UNREACHABLE,
					"&Show unreachable nodes (by following edges against their direction)",
					getFieldEditorParent()));
//
//		addField(new RadioGroupFieldEditor(
//				PreferenceConstants.P_CHOICE,
//			"An example of a multiple-choice preference",
//			1,
//			new String[][] { { "&Choice 1", "choice1" }, {
//				"C&hoice 2", "choice2" }
//		}, getFieldEditorParent()));
//		addField(
//			new StringFieldEditor(PreferenceConstants.P_STRING, "A &text preference:", getFieldEditorParent()));
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	public void init(IWorkbench workbench) {
	}
	
}