package de.uni_freiburg.informatik.ultimate.plugins.output.lazyabstractiononcfg.preferences;

import org.eclipse.jface.preference.*;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.IWorkbench;

import de.uni_freiburg.informatik.ultimate.plugins.output.lazyabstractiononcfg.Activator;

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

public class LAOnCFGPreferencePage
	extends FieldEditorPreferencePage
	implements IWorkbenchPreferencePage {

	public LAOnCFGPreferencePage() {
		super(GRID);
		setPreferenceStore(Activator.getDefault().getPreferenceStore());
		setDescription("Preferences for the Lazy Abstraction on CFG Plugin");
	}
	
	/**
	 * Creates the field editors. Field editors are abstractions of
	 * the common GUI blocks needed to manipulate various types
	 * of preferences. Each field editor knows how to save and
	 * restore itself.
	 */
	public void createFieldEditors() {
		addField(new IntegerFieldEditor(PreferenceConstants.P_MAX_STEPS,
				"&Maximum number of iterations before timeout", getFieldEditorParent()));		
		addField(new DirectoryFieldEditor(PreferenceConstants.P_IMAGE_PATH, 
				"&Directory for writing the graphs (empty for don't write):", getFieldEditorParent()));
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
//		addField(
//				new BooleanFieldEditor(
//					PreferenceConstants.P_ONLY_SELFLOOPS,
//					"&only for self loops it is checked if the annotation is an invariant " +
//					"\n when this is true, m_dontBendFromCopies does not matter - it's as if it were true\n" +
//					" not a sensible option though, as loops ranging over more than one node cannot be proven correct\n" +
//					"(if they do something relevant..)",
//					getFieldEditorParent()));
		addField(
				new BooleanFieldEditor(
					PreferenceConstants.P_DONTBEND_FROM_NONCOPIES,
					"&don't check \"old\" edges, only the newly created ones coming from the new copies",
					getFieldEditorParent()));
//		addField(
//			new BooleanFieldEditor(
//				PreferenceConstants.P_BOOLEAN,
//				"&An example of a boolean preference",
//				getFieldEditorParent()));
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