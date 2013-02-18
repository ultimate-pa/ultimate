package local.stalin.SMTInterface.preferences;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;

public class BooleanFieldEditorFreed extends BooleanFieldEditor {

	public BooleanFieldEditorFreed() {
		// TODO Auto-generated constructor stub
	}

	public BooleanFieldEditorFreed(String name, String label, Composite parent) {
		super(name, label, parent);
		// TODO Auto-generated constructor stub
	}

	public BooleanFieldEditorFreed(String name, String labelText, int style,
			Composite parent) {
		super(name, labelText, style, parent);
		// TODO Auto-generated constructor stub
	}

	public Button getChangeButtonControl(Composite parent)
	{
		return this.getChangeControl(parent);		
	}
		
}
