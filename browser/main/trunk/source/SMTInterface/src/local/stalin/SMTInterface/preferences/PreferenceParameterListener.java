package local.stalin.SMTInterface.preferences;

import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;

public class PreferenceParameterListener implements Listener {

	private PreferencePage m_preferencePage; 
	
	public PreferenceParameterListener(PreferencePage preferencePage) {
		this.m_preferencePage = preferencePage;
	}

	@Override
	public void handleEvent(Event event) {
		this.m_preferencePage.updateCommandLineOptions();	
	}

}
