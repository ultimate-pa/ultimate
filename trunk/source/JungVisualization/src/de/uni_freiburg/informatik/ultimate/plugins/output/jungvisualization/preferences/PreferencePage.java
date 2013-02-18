package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.preferences;

import java.io.IOException;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;


/**
 * Preference page for the JungVisualiation plug-in.
 * @see {@link FieldEditorPreferencePage}
 * @see {@link IWorkbenchPreferencePage}
 * 
 * @author lena
 *
 */
public class PreferencePage extends FieldEditorPreferencePage implements
IWorkbenchPreferencePage {
	
	private final ScopedPreferenceStore preferences;

	public PreferencePage(){
		super(GRID);
		preferences = PreferenceValues.Preference;
		setPreferenceStore(preferences);
		}
	
	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.preference.FieldEditorPreferencePage#createFieldEditors()
	 */
	@Override
	protected void createFieldEditors() {	
		
		addField(new DirectoryFieldEditor(PreferenceValues.NAME_PATH,PreferenceValues.LABEL_PATH, getFieldEditorParent()));
		
		addField(new BooleanFieldEditor(PreferenceValues.NAME_ANNOTATED_EDGES, PreferenceValues.LABEL_ANNOTATED_EDGES, getFieldEditorParent()));
		
		addField(new BooleanFieldEditor(PreferenceValues.NAME_ANNOTATED_NODES, PreferenceValues.LABEL_ANNOTATED_NODES, getFieldEditorParent()));
		
		addField(new ComboFieldEditor(PreferenceValues.NAME_LAYOUT, PreferenceValues.LABEL_LAYOUT, 
					new String[][]{{"FRLayout", "FRLayout"},
				   				   {"FRLayout2", "FRLayout2"},
				   				   {"ISOMLayout", "ISOMLayout"},
				   				   {"KKLayout", "KKLayout"},
				   				   {"TreeLayout", "TreeLayout"}
				   				   }, getFieldEditorParent()));
		
//		addField(new RadioGroupFieldEditor(PreferenceValues.NAME_LAYOUT, PreferenceValues.LABEL_LAYOUT, 2, 
//											new String[][]{{"FRLayout", "FRLayout"},
//														   {"FRLayout2", "FRLayout2"},
//														   {"ISOMLayout", "ISOMLayout"},
//														   {"KKLayout", "KKLayout"}}, getFieldEditorParent()));
		addField(new ColorFieldEditor(PreferenceValues.NAME_COLOR_BACKGROUND, PreferenceValues.LABEL_COLOR_BACKGROUND, getFieldEditorParent()));
		addField(new ColorFieldEditor(PreferenceValues.NAME_COLOR_NODE, PreferenceValues.LABEL_COLOR_NODE, getFieldEditorParent()));
		addField(new ColorFieldEditor(PreferenceValues.NAME_COLOR_NODE_PICKED, PreferenceValues.LABEL_COLOR_NODE_PICKED, getFieldEditorParent()));
		addField(new RadioGroupFieldEditor(PreferenceValues.NAME_SHAPE_NODE, PreferenceValues.LABEL_SHAPE_NODE, 1, 
				new String[][]{{"Round rectangle", "RoundRectangle"},
							   {"Rectangle", "Rectangle"},
							   {"Ellipse", "Ellipse"}}, getFieldEditorParent()));		
	}
	
	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.preference.FieldEditorPreferencePage#performOk()
	 */
	public boolean performOk() {
		try {
			preferences.save();
			//logger.debug("Saved JV Preferences");
		} catch (IOException ioe) {
			//logger.warn(ioe);
			ioe.printStackTrace(System.err);
		}
		return super.performOk();
	}
	
	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	@Override
	public void init(IWorkbench workbench) {
	
	}

}
