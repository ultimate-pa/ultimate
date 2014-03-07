package de.uni_freiburg.informatik.ultimate.gui.views;

import de.uni_freiburg.informatik.ultimate.gui.interfaces.IPayloadSelection;
import de.uni_freiburg.informatik.ultimate.gui.provider.AnnotationTreeProvider;
import de.uni_freiburg.informatik.ultimate.gui.provider.AnnotationsLabelProvider;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.progress.UIJob;

/**
 * A nodeViewer so we can present selected nodes to the user...
 * 
 * @author dietsch
 * 
 */
public class NodeView extends ViewPart implements ISelectionListener {


	public static final String ID = "de.uni_freiburg.informatik.ultimate.plugins.output.graphview2d.views.NodeView";

	private TreeViewer treeViewer;

	public NodeView(){
		super();
	}
	
	public void dispose() {
		getSite().getWorkbenchWindow().getSelectionService()
				.removeSelectionListener(this);
		super.dispose();
	}

	//@Override
	public void createPartControl(Composite parent) {
		treeViewer = new TreeViewer(parent, SWT.BORDER | SWT.MULTI
				| SWT.V_SCROLL);
		treeViewer.setLabelProvider(new AnnotationsLabelProvider());
		treeViewer.setContentProvider(new AnnotationTreeProvider());
		getSite().getPage().addSelectionListener(this);
	}

	//@Override
	public void setFocus() {
		treeViewer.getControl().setFocus();
	}

	public void selectionChanged(IWorkbenchPart part, final ISelection selection) {
		if (selection instanceof IPayloadSelection) {
			UIJob job = new UIJob("Selection changed...") {
				public IStatus runInUIThread(IProgressMonitor mon) {
					treeViewer.setSelection(null);
					treeViewer.setInput(((IPayloadSelection) selection).getPayload());
					treeViewer.expandAll();
					treeViewer.refresh();
					return Status.OK_STATUS;
				}
			};
			job.setPriority(UIJob.INTERACTIVE); 
			job.schedule(); 
		}
	}
	
	
	
	
	

}
