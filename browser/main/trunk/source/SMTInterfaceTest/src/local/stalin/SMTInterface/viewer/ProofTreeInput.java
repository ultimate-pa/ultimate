package local.stalin.SMTInterface.viewer;

import local.stalin.nativez3.Z3ProofRule;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IPersistableElement;

public class ProofTreeInput implements IEditorInput {

	private Z3ProofRule mroot;
	private String mname;
	
	public ProofTreeInput(Z3ProofRule root,String name) {
		mroot = root;
		mname = name;
	}
	
	@Override
	public boolean exists() {
		return mroot != null;
	}

	@Override
	public ImageDescriptor getImageDescriptor() {
		return null;
	}

	@Override
	public String getName() {
		return mname;
	}

	@Override
	public IPersistableElement getPersistable() {
		return null;
	}

	@Override
	public String getToolTipText() {
		return "Visualization of a Z3 Proof";
	}

	@Override
	@SuppressWarnings("unchecked")
	public Object getAdapter(Class adapter) {
		return null;
	}

	public Z3ProofRule getRoot() {
		return mroot;
	}
	
}
