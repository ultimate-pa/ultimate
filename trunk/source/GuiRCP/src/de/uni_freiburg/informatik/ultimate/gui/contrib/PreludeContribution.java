package de.uni_freiburg.informatik.ultimate.gui.contrib;

import java.io.File;
import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.gui.GuiController;
import de.uni_freiburg.informatik.ultimate.gui.interfaces.IPreferencesKeys;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.menus.WorkbenchWindowControlContribution;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

public class PreludeContribution extends WorkbenchWindowControlContribution {

	public final static String s_ID = "de.uni_freiburg.informatik.ultimate.gui.contrib.Prelude";
	
	private static PreludeContribution s_me;
	
	public static final File getPreludeFile() {
		String pl = s_me.getPrelude();
		return pl == null ? null : new File(pl);
	}
	
	private String m_preludeFile = null;

	private void init() {
		s_me = this;
		InstanceScope iscope = new InstanceScope();
        IEclipsePreferences prefscope = iscope.getNode(GuiController.sPLUGINID);
        m_preludeFile = prefscope.get(IPreferencesKeys.PRELUDEFILE, null);
        if (m_preludeFile != null) {
	        File tmp = new File(m_preludeFile);
	        if (!tmp.canRead()) {
	        	m_preludeFile = null;
	        	prefscope.remove(IPreferencesKeys.PRELUDEFILE);
	        }
        }
	}
	
	@Override
	public void dispose() {
		InstanceScope iscope = new InstanceScope();
        ScopedPreferenceStore store = new ScopedPreferenceStore(iscope,GuiController.sPLUGINID);
        IEclipsePreferences prefscope = iscope.getNode(GuiController.sPLUGINID);
        if (m_preludeFile != null)
        	prefscope.put(IPreferencesKeys.PRELUDEFILE,m_preludeFile);
        else
        	prefscope.remove(IPreferencesKeys.PRELUDEFILE);
		try {
			store.save();
		} catch (IOException e) {
			e.printStackTrace();
		}
		super.dispose();
	}

	public PreludeContribution() {
		init();
	}

	public PreludeContribution(String id) {
		super(id);
		init();
	}

	@Override
	protected Control createControl(Composite parent) {
		final GridLayout gridLayout = new GridLayout();
		gridLayout.numColumns = 3;
		Composite comp = new Composite(parent,SWT.NONE);
		final Text label = new Text(comp,SWT.SINGLE|SWT.READ_ONLY|SWT.RIGHT);
		if (m_preludeFile != null) {
			File tmp = new File(m_preludeFile);
			label.setText(tmp.getName());
			label.setToolTipText(m_preludeFile);
		}
		Button button = new Button(comp,SWT.PUSH);
		button.setText("Change Prelude");
		button.addListener(SWT.Selection, new Listener() {

			@Override
			public void handleEvent(Event arg0) {
				try {
				FileDialog diag = new FileDialog(
						getWorkbenchWindow().getShell(),SWT.OPEN);
				diag.setFileName(getPrelude());
				String res = diag.open();
				if (res != null) {
					label.setText(new File(res).getName());
					label.setToolTipText(res);
					label.pack();
					label.getParent().pack();
					m_preludeFile = res;
				}
				} catch (Exception exc) {
					exc.printStackTrace(System.err);
				}
			}
			
		});
		Button reset = new Button(comp,SWT.PUSH);
		reset.setText("Unset Prelude");
		reset.addListener(SWT.Selection, new Listener() {

			@Override
			public void handleEvent(Event arg0) {
				label.setText("");
				label.setToolTipText("");
				m_preludeFile = null;
			}
			
		});
		label.setLayoutData(new GridData());
		button.setLayoutData(new GridData());
		reset.setLayoutData(new GridData());
		comp.setLayout(gridLayout);
		return comp;
	}
	
	public String getPrelude() {
		return m_preludeFile;
	}

}
