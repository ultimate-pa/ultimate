package local.stalin.SMTInterface.preferences.nativez3;

import local.stalin.SMTInterface.Activator;
import local.stalin.SMTInterface.preferences.nativez3.NativeZ3PreferencePage.Z3ConfigParam;

import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.StatusDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.VerifyEvent;
import org.eclipse.swt.events.VerifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

public class ConfigParamDialog extends StatusDialog {
	private class ConfigVerify implements VerifyListener {

		@Override
		public void verifyText(VerifyEvent e) {
			doValidation();
		}
		
	}
	
	private Z3ConfigParam mparam;
	private Text mname;
	private Text mvalue;
	private String mnameval;
	private String mvalueval;
	
	public ConfigParamDialog(Shell parent,Z3ConfigParam param) {
		super(parent);
		mparam = param;
		if( param == null )
			setTitle("Create new Z3 Config Parameter");
		else
			setTitle("Edit Z3 Config Parameter");
	}

	@Override
	protected Control createDialogArea(Composite parent) {
		VerifyListener vl = new ConfigVerify();
		Composite comp = (Composite)super.createDialogArea(parent);
		Label namelabel = new Label(comp,SWT.NONE);
		namelabel.setText("&Name:");
		mname = new Text(comp,SWT.BORDER);
		mname.addVerifyListener(vl);
		Label valuelabel = new Label(comp,SWT.NONE);
		valuelabel.setText("&Value:");
		mvalue = new Text(comp,SWT.BORDER);
		if( mparam != null ) {
			mname.setText(mparam.param);
			mvalue.setText(mparam.value);
		}
		GridLayout gl = new GridLayout(2,false);
		comp.setLayout(gl);
		namelabel.setLayoutData(new GridData());
		mname.setLayoutData(new GridData());
		valuelabel.setLayoutData(new GridData());
		mvalue.setLayoutData(new GridData());
		return comp;
	}

	public Z3ConfigParam getResult() {
		if( mparam == null )
			mparam = new NativeZ3PreferencePage.Z3ConfigParam();
		mparam.param = mnameval;
		mparam.value = mvalueval;
		return mparam;
	}
	
	private void doValidation() {
		String name = mname.getText();
		int end = name.length();
		Status status = new Status(Status.OK,Activator.PLUGIN_ID,"No error");
		for( int i = 0; i < end; ++i ) {
			char c = name.charAt(i);
			if( Character.isWhitespace(c) ) {
				status = new Status(Status.ERROR,Activator.PLUGIN_ID,"Z3 Configuration Name is not allowed to contain spaces");
				break;
			}
			if( !Character.isLetter(c) && c != '_' ) {
				status = new Status(Status.ERROR,Activator.PLUGIN_ID,"Z3 Configuration Name may only contain letters and underscores");
				break;
			}
		}
		updateStatus(status);
	}

	@Override
	public boolean close() {
		mnameval = mname.getText().trim();
		mvalueval = mvalue.getText().trim();
		return super.close();
	}
	
}
