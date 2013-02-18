package local.stalin.SMTInterface.preferences;

import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;

import local.stalin.SMTInterface.Activator;
import local.stalin.SMTInterface.preferences.PreferenceCommandLineOptions.BoolCLO;
import local.stalin.SMTInterface.preferences.PreferenceCommandLineOptions.IntCLO;
import local.stalin.SMTInterface.preferences.PreferenceCommandLineOptions.CommandLineOption;
import local.stalin.core.api.StalinServices;

import org.apache.log4j.Logger;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.*;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

/**
 * the preference page for the 2dgraph plugin should also serve as template for
 * other pluginspref-pages
 * 
 * this calls contributes to the extensionpoint: org.eclipse.ui.prefgerencePages
 * see at the plugin.xml
 * 
 * @author Christian Ortolf
 */
public class PreferencePage extends FieldEditorPreferencePage implements
		IWorkbenchPreferencePage {

	public static final Logger logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	private final ScopedPreferenceStore preferences;
	private FileFieldEditor smtexecutable;
	private StringFieldEditor smtparameter;
	private DirectoryFieldEditor temppath;
	private StringFieldEditor customParms;
	private StringFieldEditor optionPrefix;
	private BooleanFieldEditor storesmtlibfiles;
	
	private RadioGroupFieldEditor solverselection;
	
	private HashMap<String,FieldEditor> fieldeditors;
	
	// z3 options
	private PreferenceCommandLineOptions z3options; 
	private Group z3optionsgroup;	
	
	
	// yices options
	private PreferenceCommandLineOptions yicesoptions;
	private Group yicesoptionsgroup;	

	public PreferencePage() {
		super(GRID);
		preferences = PreferenceValues.Preference;
		setPreferenceStore(preferences);
		this.z3options = PreferenceCommandLineOptions.getZ3Options();
		this.yicesoptions = PreferenceCommandLineOptions.getYicesOptions();
		this.fieldeditors = new HashMap<String,FieldEditor>();

	}

	protected RadioGroupFieldEditor getSolverSelectionFieldEditor()
	{
		return solverselection;	
	}
	
	protected void updateCommandLineOptions()
	{
		boolean z3selected = ((Button)solverselection.getRadioBoxControl(getFieldEditorParent()).getChildren()[0]).getSelection();
		PreferenceCommandLineOptions options;
		if (z3selected)
		{
			options = this.z3options;
		}
		else
		{
			options = this.yicesoptions;
		}

		options.setCustomparameters(customParms.getStringValue());
		options.setOptionPrefix(optionPrefix.getStringValue());
		
		Iterator<String> it = options.getAllOptions().keySet().iterator();
		while(it.hasNext()) 
		{	
			String optionName = it.next();
			CommandLineOption theOption = options.getAllOptions().get(optionName);
			if (theOption.getClass() == BoolCLO.class)
			{
				BoolCLO boolOption = (BoolCLO)theOption;
				BooleanFieldEditorFreed boolEditor = (BooleanFieldEditorFreed)this.fieldeditors.get(optionName);
				boolOption.setCurrentValue(boolEditor.getBooleanValue());
			}
			else if (theOption.getClass() == IntCLO.class)
			{
				IntCLO intOption = (IntCLO)theOption;
				StringFieldEditor intEditor = (StringFieldEditor)this.fieldeditors.get(optionName);
				intOption.setCurrentValue(Integer.parseInt(intEditor.getStringValue()));
			}			 
		}
		this.updateParameterField();
	}
	
	protected void updateParameterField()
	{
		boolean z3selected = ((Button)solverselection.getRadioBoxControl(getFieldEditorParent()).getChildren()[0]).getSelection();
		if (z3selected)
		{
			this.smtparameter.setStringValue(this.z3options.getParameters());			
		}
		else
		{
			this.smtparameter.setStringValue(this.yicesoptions.getParameters());	
		}		
	}
			
	private void createFieldEditors(Composite parent, PreferenceCommandLineOptions options)
	{
		PreferenceParameterListener paramlistener = new PreferenceParameterListener(this);
		Iterator<String> it = options.getAllOptions().keySet().iterator();
		while(it.hasNext())
		{	
			String optionName = it.next();
			CommandLineOption theOption = options.getAllOptions().get(optionName);
			if (theOption.getClass() == BoolCLO.class)
			{
				// we got a boolean
				BoolCLO boolOption = (BoolCLO)theOption;
				BooleanFieldEditorFreed newFieldEditor = new BooleanFieldEditorFreed(optionName,
						theOption.getLabel(),
						parent);
				newFieldEditor.getChangeButtonControl(parent).addListener(SWT.Selection, paramlistener);
				addField(newFieldEditor);
				this.fieldeditors.put(optionName, newFieldEditor);
				preferences.setDefault(optionName,
						boolOption.getDefaultValue());
			}
			if (theOption.getClass() == IntCLO.class)
			{
				IntCLO intOption = (IntCLO)theOption;
				StringFieldEditor newFieldEditor = new StringFieldEditor(optionName,
						theOption.getLabel(),
						7,
						parent);
				newFieldEditor.getTextControl(parent).addListener(SWT.KeyUp, paramlistener);
				//newFieldEditor.fillIntoGrid(parent, 2);
				//newFieldEditor.s
				addField(newFieldEditor);
				this.fieldeditors.put(optionName, newFieldEditor);
				preferences.setDefault(optionName,
						intOption.getDefaultValue());
			}
		}
	}
	
	protected Composite getFEParent()
	{
		return getFieldEditorParent();
	}
	
	protected void activateZ3View()
	{				
//		this.yicesoptionsgroup.setVisible(false);
//		this.z3optionsgroup.setVisible(true);
	}
	
	
	protected void activateYicesView()
	{
//		this.z3optionsgroup.setVisible(false);
//		this.yicesoptionsgroup.setVisible(true);
	}
		
	
	//@Override
	protected void createFieldEditors() {
		
		String [][] solverradiobuttons = new String[][] {
				{PreferenceValues.LABEL_Z3, "z3"},
				{PreferenceValues.LABEL_YICES, "yices"}
		};
		solverselection = new RadioGroupFieldEditor(
				PreferenceValues.NAME_SOLVERSELECTION,
				PreferenceValues.LABEL_SOLVERSELECTION,
				2,
				solverradiobuttons,
				getFieldEditorParent(),
				true);
		
		smtexecutable = new FileFieldEditor(
				PreferenceValues.NAME_SMTEXECUTABLE,
				PreferenceValues.LABEL_SMTEXECUTABLE, getFieldEditorParent());

		storesmtlibfiles = new BooleanFieldEditor(PreferenceValues.NAME_SAVESMTLIBFILES,
				PreferenceValues.LABEL_SAVESMTLIBFILES,getFieldEditorParent());

		PreferenceParameterListener paramlistener = new PreferenceParameterListener(this);		
		
		customParms = new StringFieldEditor(PreferenceValues.NAME_CUSTOMPARMS,
				PreferenceValues.LABEL_CUSTOMPARMS, getFieldEditorParent());
		
		customParms.getTextControl(getFieldEditorParent()).addListener(SWT.Modify, paramlistener);
		
		optionPrefix = new StringFieldEditor(PreferenceValues.NAME_OPTION_PREFIX,
				PreferenceValues.LABEL_OPTION_PREFIX, getFieldEditorParent());
		optionPrefix.getTextControl(getFieldEditorParent()).addListener(SWT.Modify, paramlistener);
		optionPrefix.getTextControl(getFieldEditorParent()).setTextLimit(2);
		
		smtparameter = new StringFieldEditor(
				PreferenceValues.NAME_SMTPARAMETER,
				PreferenceValues.LABEL_SMTPARAMETER, getFieldEditorParent());
		
		smtparameter.getTextControl(getFieldEditorParent()).setEditable(false);

		temppath = new DirectoryFieldEditor(PreferenceValues.NAME_TEMPPATH,
				PreferenceValues.LABEL_TEMPPATH, getFieldEditorParent());


		PreferenceSolverSelectionListener solverswitchListener = new PreferenceSolverSelectionListener(this);

		//solverselection.getRadioBoxControl(null).getChildren()[0].addListener(SWT.Selection, solverswitchListener);
		solverselection.getRadioBoxControl(getFieldEditorParent()).getChildren()[0].addListener(SWT.Selection, solverswitchListener);
		solverselection.getRadioBoxControl(getFieldEditorParent()).getChildren()[1].addListener(SWT.Selection, solverswitchListener);
		
		// z3
		this.z3optionsgroup = new Group(getFieldEditorParent(),SWT.SHADOW_NONE);
		this.z3optionsgroup.setText("Z3 Options");
		GridLayout groupGridL = new GridLayout();
		groupGridL.numColumns = 2;
		groupGridL.makeColumnsEqualWidth = true;
		this.z3optionsgroup.setLayout(groupGridL);
		this.createFieldEditors(this.z3optionsgroup,this.z3options);
		//this.createFieldEditors(getFieldEditorParent(),this.z3options);
		//this.fieldeditors.put(PreferenceValues.NAME_Z3_DIMACS, dimacs);
		
		// yices
		this.yicesoptionsgroup = new Group(getFieldEditorParent(),SWT.SHADOW_NONE);
		this.yicesoptionsgroup.setText("Yices Options");
		this.createFieldEditors(this.yicesoptionsgroup,this.yicesoptions);
		//this.createFieldEditors(getFieldEditorParent(),this.yicesoptions);
		
		//this.fieldeditors.put(PreferenceValues.NAME_YICES_CONSERVATIVE, conservative);
				
		addField(storesmtlibfiles);
		addField(solverselection);
		addField(smtexecutable);
		addField(customParms);
		addField(optionPrefix);
		addField(smtparameter);
		addField(temppath);
		
		
		//activateZ3View();

		preferences.setDefault(PreferenceValues.NAME_SOLVERSELECTION,
				PreferenceValues.VALUE_SOLVERSELECTION_DEFAULT);
		preferences.setDefault(PreferenceValues.NAME_SMTEXECUTABLE,
				PreferenceValues.VALUE_SMTEXECUTABLE_DEFAULT);
		preferences.setDefault(PreferenceValues.NAME_SMTPARAMETER,
				PreferenceValues.VALUE_SMTPARAMETER_DEFAULT);
		preferences.setDefault(PreferenceValues.NAME_TEMPPATH,
				PreferenceValues.VALUE_TEMPPATH_DEFAULT);
		preferences.setDefault(PreferenceValues.NAME_CUSTOMPARMS,
				PreferenceValues.VALUE_CUSTOMPARMS_DEFAULT);
		preferences.setDefault(PreferenceValues.NAME_OPTION_PREFIX,
				PreferenceValues.VALUE_OPTION_PREFIX_DEFAULT);
		preferences.setDefault(PreferenceValues.NAME_SAVESMTLIBFILES,
				PreferenceValues.VALUE_SAVESMTLIBFILES);
	}

	public boolean performOk() {
		try {
			preferences.save();
			logger.debug("Saved SMT Preferences");
		} catch (IOException ioe) {
			logger.warn(ioe);
		}
		return super.performOk();
	}

	protected IPreferenceStore doGetPreferenceStore() {
		return preferences;
	}

	public void init(IWorkbench workbench) {

	}
}
