package local.stalin.SMTInterface.preferences;

import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;

public class PreferenceSolverSelectionListener implements Listener {

	private PreferencePage m_preferencePage; 
	
	public PreferenceSolverSelectionListener(PreferencePage preferencePage) {
		this.m_preferencePage = preferencePage;
	}

	@Override
	public void handleEvent(Event event) {
		//String solversel = this.m_preferencePage.getPreferenceStore().getString(PreferenceValues.NAME_SOLVERSELECTION);
		boolean z3selected = ((Button)this.m_preferencePage.getSolverSelectionFieldEditor().getRadioBoxControl(this.m_preferencePage.getFEParent()).getChildren()[0]).getSelection();
		//boolean yicesselected = ((Button)this.m_preferencePage.getSolverSelectionFieldEditor().getRadioBoxControl(this.m_preferencePage.getFEParent()).getChildren()[1]).getSelection();
		if (z3selected)
		{				
			//this.m_preferencePage.activateZ3View();				
		}
		else
		{
			// yices selected				
			//this.m_preferencePage.activateYicesView();				
		}	
		this.m_preferencePage.updateCommandLineOptions();
		this.m_preferencePage.updateParameterField();
		
		//this.m_preferencePage.updateParameterField("trest");	
	}

}
