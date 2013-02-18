package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.preferences;

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.actions.EdgeLabel;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.gui.PrefuseColorSelection;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.gui.PrefuseFontSelection;

import org.apache.log4j.Logger;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.FontFieldEditor;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;

import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import prefuse.data.Schema;
import prefuse.util.FontLib;
import prefuse.visual.VisualItem;

/**
 * the preference page for the prefuse visualization plugin
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate: 2008-03-07 13:50:06 +0100 (Fr, 07 Mrz 2008) $
 * $LastChangedBy: keilr $
 * $LastChangedRevision: 495 $ 
 */
public class PreferencePage extends FieldEditorPreferencePage implements
		IWorkbenchPreferencePage {

	public static final Logger logger = Logger.getLogger(PreferencePage.class);
	private final ScopedPreferenceStore preferences;
	
	private RadioGroupFieldEditor DISPLAYCHOOSERECUTABLE;
	private ComboFieldEditor STANDARTDISPLAY;

	private ColorFieldEditor NODESTYLECOLOR;
	private ColorFieldEditor NODEMARKCOLOR;
	private ColorFieldEditor NODEOVERCOLOR;
	private ColorFieldEditor TEXTSTYLECOLOR_LEAF;
	private ColorFieldEditor TEXTSTYLECOLOR_UNDEFIENEDTOKEN;
	private ColorFieldEditor TEXTSTYLECOLOR_TOKEN;
	private ColorFieldEditor TEXTMARKCOLOR;
	private ColorFieldEditor TEXTOVERCOLOR;
	private ColorFieldEditor EDGESTYLECOLOR;

	private FontFieldEditor NODEFONT;
	
	
	/**
	 * constructor
	 */
	public PreferencePage() {
		super(GRID);
		preferences = PreferenceValues.Preference;
		setPreferenceStore(preferences);
	}

	//@Override
	protected void createFieldEditors() {
		DISPLAYCHOOSERECUTABLE = new RadioGroupFieldEditor(
				PreferenceValues.NAME_DISPLAYCHOOSERECUTABLE,
				PreferenceValues.LABEL_DISPLAYCHOOSERECUTABLE, 1,
				PreferenceValues.VALUES_DISPLAYCHOOSERECUTABLE,
				getFieldEditorParent());

		STANDARTDISPLAY = new ComboFieldEditor(
				PreferenceValues.NAME_STANDARDDISPLAY,
				PreferenceValues.LABEL_STANDARDDISPLAY,
				PreferenceValues.VALUES_STANDARDDISPLAY, getFieldEditorParent());

		NODESTYLECOLOR = new ColorFieldEditor(
				PreferenceValues.NAME_NODESTYLECOLOR,
				PreferenceValues.LABEL_NODESTYLECOLOR, getFieldEditorParent());

		NODEMARKCOLOR = new ColorFieldEditor(
				PreferenceValues.NAME_NODEMARKCOLOR,
				PreferenceValues.LABEL_NODEMARKCOLOR, getFieldEditorParent());

		NODEOVERCOLOR = new ColorFieldEditor(
				PreferenceValues.NAME_NODEOVERCOLOR,
				PreferenceValues.LABEL_NODEOVERCOLOR, getFieldEditorParent());

		TEXTSTYLECOLOR_LEAF = new ColorFieldEditor(
				PreferenceValues.NAME_TEXTSTYLECOLOR_LEAF,
				PreferenceValues.LABEL_TEXTSTYLECOLOR_LEAF,
				getFieldEditorParent());

		TEXTSTYLECOLOR_UNDEFIENEDTOKEN = new ColorFieldEditor(
				PreferenceValues.NAME_TEXTSTYLECOLOR_UNDEFIENEDTOKEN,
				PreferenceValues.LABEL_TEXTSTYLECOLOR_UNDEFIENEDTOKEN,
				getFieldEditorParent());

		TEXTSTYLECOLOR_TOKEN = new ColorFieldEditor(
				PreferenceValues.NAME_TEXTSTYLECOLOR_TOKEN,
				PreferenceValues.LABEL_TEXTSTYLECOLOR_TOKEN,
				getFieldEditorParent());

		TEXTMARKCOLOR = new ColorFieldEditor(
				PreferenceValues.NAME_TEXTMARKCOLOR,
				PreferenceValues.LABEL_TEXTMARKCOLOR, getFieldEditorParent());

		TEXTOVERCOLOR = new ColorFieldEditor(
				PreferenceValues.NAME_TEXTOVERCOLOR,
				PreferenceValues.LABEL_TEXTOVERCOLOR, getFieldEditorParent());

		EDGESTYLECOLOR = new ColorFieldEditor(
				PreferenceValues.NAME_EDGESTYLECOLOR,
				PreferenceValues.LABEL_EDGESTYLECOLOR, getFieldEditorParent());

		NODEFONT = new FontFieldEditor(PreferenceValues.NAME_NODEFONT,
				PreferenceValues.LABEL_NODEFONT, getFieldEditorParent());
		

		// load default values
		PreferenceValues.initializeDefaultPreferences();
		
		addField(DISPLAYCHOOSERECUTABLE);
		addField(STANDARTDISPLAY);
		addField(NODESTYLECOLOR);
		addField(NODEMARKCOLOR);
		addField(NODEOVERCOLOR);
		addField(TEXTSTYLECOLOR_LEAF);
		addField(TEXTSTYLECOLOR_UNDEFIENEDTOKEN);
		addField(TEXTSTYLECOLOR_TOKEN);
		addField(TEXTMARKCOLOR);
		addField(TEXTOVERCOLOR);
		addField(EDGESTYLECOLOR);
		addField(NODEFONT);	
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.preference.FieldEditorPreferencePage#performOk()
	 */
	public boolean performOk() {
		try {
			preferences.save();	
			logger.debug("Saved Prefuse Preferences");
		} catch (IOException ioe) {
			logger.warn(ioe);
		}
		
		//  sets the edge deco
		Schema DECORATOR_SCHEMA = EdgeLabel.getDecorator();
		PrefuseFontSelection prefuseFontSelection = new PrefuseFontSelection();
		PrefuseColorSelection prefuseColorSelection = new PrefuseColorSelection();
		
		DECORATOR_SCHEMA.setDefault(VisualItem.INTERACTIVE, false);
		DECORATOR_SCHEMA.setDefault(VisualItem.TEXTCOLOR, prefuseColorSelection
				.getEdgeStyleColor());
		DECORATOR_SCHEMA.setDefault(VisualItem.FILLCOLOR, prefuseColorSelection
				.getNodeStyleColor(""));
		DECORATOR_SCHEMA.setDefault(VisualItem.FONT, FontLib.getFont(prefuseFontSelection
				.getNodeFont().getFontName(), prefuseFontSelection.getNodeFont().getSize()-1 ));
		
		EdgeLabel.setDecorator(DECORATOR_SCHEMA);
		
		return super.performOk();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.preference.PreferencePage#doGetPreferenceStore()
	 */
	protected IPreferenceStore doGetPreferenceStore() {
		return preferences;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	public void init(IWorkbench workbench) {
	}
}