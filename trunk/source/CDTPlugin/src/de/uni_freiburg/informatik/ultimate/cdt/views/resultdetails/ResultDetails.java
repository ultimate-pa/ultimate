/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.views.resultdetails;

import java.util.List;
import java.util.regex.Pattern;

import org.eclipse.cdt.codan.core.model.ICodanProblemMarker;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.ISelectionService;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.MarkerUtilities;

import de.uni_freiburg.informatik.ultimate.cdt.codan.CDTResultStore;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.IResultWithLocation;

/**
 * This new View is basically a replacement for the not really handy
 * ProblemDetails-View, provided by Codan itself.
 * 
 * @author Stefan Wissert
 * 
 */
public class ResultDetails extends ViewPart {

	public static String ID = "de.uni_freiburg.informatik.ultimate.cdt.ResultDetails";

	/**
	 * The underlying JFace Component
	 */
	private TextViewer viewer;

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets
	 * .Composite)
	 */
	@Override
	public void createPartControl(Composite parent) {
		final String problemsViewId = "org.eclipse.ui.views.ProblemView";
		viewer = new TextViewer(parent, SWT.BORDER | SWT.H_SCROLL
				| SWT.V_SCROLL | SWT.FULL_SELECTION);
		viewer.setEditable(false);
		ISelectionService ser = (ISelectionService) getSite().getService(
				ISelectionService.class);
		ser.addSelectionListener(new ISelectionListener() {
			public void selectionChanged(IWorkbenchPart part,
					ISelection selection) {
				if (part.getSite().getId().equals(problemsViewId)) {
					processSelection(selection);
				}
			}
		});
		ISelection selection = ser.getSelection(problemsViewId);
		processSelection(selection);
	}

	protected void processSelection(ISelection selection) {
		if (selection == null || selection.isEmpty())
			return;
		if (selection instanceof IStructuredSelection) {
			Object firstElement = ((IStructuredSelection) selection)
					.getFirstElement();
			IMarker marker = null;
			if (firstElement instanceof IAdaptable) {
				marker = (IMarker) ((IAdaptable) firstElement)
						.getAdapter(IMarker.class);
			} else if (firstElement instanceof IMarker) {
				marker = (IMarker) firstElement;
			}
			if (marker != null) {
				queryProviders(marker);
			}
		}
	}

	private void queryProviders(IMarker marker) {
		// First we need the complete Path for getting all Results
		
		String path = marker.getResource().getLocation().toOSString();
		int lineNumber = MarkerUtilities.getLineNumber(marker);
		String id = marker.getAttribute(ICodanProblemMarker.ID, "id");
		String[] parts = id.split(Pattern.quote("."));
		String resName = parts[parts.length - 1];
		List<IResult> results = CDTResultStore.getResults(path);
		IResultWithLocation foundRes = null;
		for (IResult ires : results) {
			if (ires instanceof IResultWithLocation) {
				IResultWithLocation res = (IResultWithLocation) ires;
				if (res.getLocation().getStartLine() == lineNumber) {
					if (resName.equals(res.getClass().getSimpleName())) {
						foundRes = res;
						break;
					}
				}
			} else {
				
			}
		}
		StringBuilder sb = new StringBuilder();
		if (foundRes != null) {
			sb.append("Result found in " + foundRes.getLocation().getFileName()
					+ " in Line: " + foundRes.getLocation().getStartLine());
			sb.append(System.getProperty("line.separator"));
			sb.append(System.getProperty("line.separator"));
			sb.append("Short Description:");
			sb.append(System.getProperty("line.separator"));
			sb.append(foundRes.getShortDescription());
			sb.append(System.getProperty("line.separator"));
			sb.append(System.getProperty("line.separator"));
			sb.append("Long Description:");
			sb.append(System.getProperty("line.separator"));
			sb.append(foundRes.getLongDescription());
		}
		Document doc = new Document(sb.toString());
		viewer.setDocument(doc);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	@Override
	public void setFocus() {
		viewer.getControl().setFocus();
	}

}
