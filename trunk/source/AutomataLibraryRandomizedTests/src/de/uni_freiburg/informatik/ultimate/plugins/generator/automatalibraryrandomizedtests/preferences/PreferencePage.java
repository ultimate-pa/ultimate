package de.uni_freiburg.informatik.ultimate.plugins.generator.automatalibraryrandomizedtests.preferences;

import org.eclipse.jface.preference.*;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.IWorkbench;

import de.uni_freiburg.informatik.ultimate.plugins.generator.automatalibraryrandomizedtests.Activator;

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

public class PreferencePage
	extends FieldEditorPreferencePage
	implements IWorkbenchPreferencePage {

	public PreferencePage() {
		super(GRID);
		setPreferenceStore(Activator.getDefault().getPreferenceStore());
		setDescription("A demonstration of a preference page implementation");
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
				PreferenceConstants.Name_WriteToFile,
				"&Write all random automata to directory specified in AutomataLibraryPreferences",
				getFieldEditorParent()));

		
		String[][] entryNamesAndValues = new String[PreferenceConstants.operations.length][2];
		for (int i=0; i<PreferenceConstants.operations.length; i++) {
			String operationName = PreferenceConstants.operations[i];
			entryNamesAndValues[i][0] = operationName;
			entryNamesAndValues[i][1] = operationName;
		}
		
		addField(new ComboFieldEditor(
				PreferenceConstants.Name_Operation, 
				"Operation that will be tested", 
				entryNamesAndValues,
				getFieldEditorParent()));
		
		IntegerFieldEditor numberOfLetters = new IntegerFieldEditor(
				PreferenceConstants.Name_NumberOfLetters, 
				PreferenceConstants.Name_NumberOfLetters,
				getFieldEditorParent(),
				6);
		numberOfLetters.setValidRange(0, 10000000);
		addField(numberOfLetters);
		
		IntegerFieldEditor numberOfStates = new IntegerFieldEditor(
				PreferenceConstants.Name_NumberOfStates, 
				PreferenceConstants.Name_NumberOfStates,
				getFieldEditorParent(),
				6);
		numberOfStates.setValidRange(0, 10000000);
		addField(numberOfStates);
		
		IntegerFieldEditor probabilityInitial = new IntegerFieldEditor(
				PreferenceConstants.Name_ProbabilityInitial, 
				PreferenceConstants.Name_ProbabilityInitial,
				getFieldEditorParent(),
				6);
		numberOfStates.setValidRange(0, 1000);
		addField(probabilityInitial);
		
		IntegerFieldEditor probabilityFinal = new IntegerFieldEditor(
				PreferenceConstants.Name_ProbabilityFinal, 
				PreferenceConstants.Name_ProbabilityFinal,
				getFieldEditorParent(),
				6);
		numberOfStates.setValidRange(0, 1000);
		addField(probabilityFinal);

		
		IntegerFieldEditor probabilityInternal = new IntegerFieldEditor(
				PreferenceConstants.Name_ProbabilityInternalTransition, 
				PreferenceConstants.Name_ProbabilityInternalTransition,
				getFieldEditorParent(),
				6);
		numberOfStates.setValidRange(0, 1000);
		addField(probabilityInternal);
		
		IntegerFieldEditor probabilityCall = new IntegerFieldEditor(
				PreferenceConstants.Name_ProbabilityCallTransition, 
				PreferenceConstants.Name_ProbabilityCallTransition,
				getFieldEditorParent(),
				6);
		numberOfStates.setValidRange(0, 1000);
		addField(probabilityCall);

		IntegerFieldEditor probabilityReturn = new IntegerFieldEditor(
				PreferenceConstants.Name_ProbabilityReturnTransition, 
				PreferenceConstants.Name_ProbabilityReturnTransition,
				getFieldEditorParent(),
				6);
		numberOfStates.setValidRange(0, 1000);
		addField(probabilityReturn);
		
		
		
		
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	public void init(IWorkbench workbench) {
	}
	
}