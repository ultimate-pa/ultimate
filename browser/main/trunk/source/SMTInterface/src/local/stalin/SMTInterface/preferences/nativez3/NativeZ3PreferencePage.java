package local.stalin.SMTInterface.preferences.nativez3;

import java.io.IOException;
import java.util.ArrayList;
import java.util.StringTokenizer;

import local.stalin.SMTInterface.Activator;
import local.stalin.core.api.StalinServices;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.ListEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

public class NativeZ3PreferencePage extends FieldEditorPreferencePage implements
		IWorkbenchPreferencePage {
	
	private final ScopedPreferenceStore store;
	
	static class Z3ConfigParam {
		public String param;
		public String value;
	}
	
	private static class Z3ConfigEditor extends ListEditor {

		public Z3ConfigEditor(String name,String labeltext,Composite parent) {
			init(name,labeltext);
			createControl(parent);
			Composite comp = getButtonBoxControl(parent);
			final Button button = new Button(comp,SWT.PUSH);
			button.setEnabled(false);
			final List list = getListControl(parent);
			Listener activationListener = new Listener() {

				@Override
				public void handleEvent(Event arg0) {
					button.setEnabled(list.getSelectionCount() != 0);
				}
				
			};
			list.addListener(SWT.Selection, activationListener);
			list.addListener(SWT.DefaultSelection, activationListener);
			button.setText("Change");
			button.setLayoutData(new GridData(SWT.HORIZONTAL));
			button.addSelectionListener(new SelectionAdapter() {

				@Override
				public void widgetSelected(SelectionEvent e) {
					Z3ConfigParam cp = new Z3ConfigParam();
					String keyval = list.getItem(list.getSelectionIndex());
					int idx = keyval.indexOf("=");
					if (idx == -1)
						return;
					cp.param = keyval.substring(0, idx);
					cp.value = keyval.substring(idx + 1);
					ConfigParamDialog cpd = new ConfigParamDialog(getShell(),cp);
					cpd.setBlockOnOpen(true);
					int res = cpd.open();
					if( res == ConfigParamDialog.OK ) {
						cp = cpd.getResult();
						String newval = cp.param + "=" + cp.value;
						list.setItem(list.getSelectionIndex(),newval);
					}
				}
				
			});
		}
		
		@Override
		protected String createList(String[] items) {
			StringBuilder sb = new StringBuilder("");
			for( String i : items ) {
				sb.append(i).append(PreferenceInitializer.SEPARATOR);
			}
			if (sb.length() > 0)
				sb.deleteCharAt(sb.length() - 1);
			return sb.toString();
		}

		@Override
		protected String getNewInputObject() {
			ConfigParamDialog cpd = new ConfigParamDialog(getShell(),null);
			cpd.setBlockOnOpen(true);
			int res = cpd.open();
			if( res == ConfigParamDialog.OK ) {
				Z3ConfigParam cp = cpd.getResult();
				return cp.param + "=" + cp.value;
			}
			return null;
		}

		@Override
		protected String[] parseString(String stringList) {
//			System.err.println("stringList = " + stringList);
			StringTokenizer st = new StringTokenizer(stringList,PreferenceInitializer.SEPARATOR);
			ArrayList<String> list = new ArrayList<String>();
			while( st.hasMoreElements() ) {
				list.add(st.nextToken());
			}
			return list.toArray(new String[list.size()]);
		}
		
	}
	
	public NativeZ3PreferencePage() {
		super(GRID);
		store = new ScopedPreferenceStore(new InstanceScope(),Activator.PLUGIN_ID);
		setPreferenceStore(store);
	}

	@Override
	protected void createFieldEditors() {
		ListEditor configs = new Z3ConfigEditor(PreferenceInitializer.NATIVEZ3CONFIG,"Z3 Configuration Parameters",getFieldEditorParent());
		addField(configs);
	}

	@Override
	public void init(IWorkbench arg0) {}

	@Override
	public boolean performOk() {
		try {
			store.save();
		} catch( IOException exc ) {
			StalinServices.getInstance().getControllerLogger().error("Unable to store Preferences for NativeZ3", exc);
		}
		return super.performOk();
	}

}
