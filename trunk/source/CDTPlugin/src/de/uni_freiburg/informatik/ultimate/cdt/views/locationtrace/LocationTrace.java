/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.views.locationtrace;

import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.navigator.CommonNavigator;
import org.eclipse.ui.part.EditorPart;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.ITextEditor;
import org.osgi.framework.Bundle;

import de.uni_freiburg.informatik.ultimate.cdt.Activator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.views.resultlist.ResultList;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;

/**
 * This is the LocationStack, where we try to list up all Locations which are in
 * the Failure-Path. It corresponds with the Selection of the FileView.
 * 
 * @author Stefan Wissert
 * 
 */
public class LocationTrace extends ViewPart implements ISelectionListener {

	/**
	 * The Id of this View
	 */
	public static String ID = "de.uni_freiburg.informatik.ultimate.cdt.LocationTrace";

	/**
	 * The underlying JFace Component.
	 */
	private TreeViewer viewer;

	/**
	 * The allowed InputFile (actual selected)
	 */
	private String actualAllowedInput = "";

	/**
	 * This list stores the current markers, which we use to highlight the
	 * counterexample in the editor.
	 */
	private List<IMarker> displayedMarkerList = new ArrayList<IMarker>();

	private LocationTraceContentProvider contProv;

	private Action stepForward;

	private Action stepBackward;

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets
	 * .Composite)
	 */
	@Override
	public void createPartControl(Composite parent) {
		Tree variableTree = new Tree(parent, SWT.BORDER | SWT.H_SCROLL
				| SWT.V_SCROLL | SWT.FULL_SELECTION);
		variableTree.setHeaderVisible(true);
		viewer = new TreeViewer(variableTree);

		TreeColumn column1 = new TreeColumn(variableTree, SWT.LEFT);
		column1.setAlignment(SWT.LEFT);
		column1.setText("Nr.");
		column1.setWidth(60);
		TreeColumn column2 = new TreeColumn(variableTree, SWT.RIGHT);
		column2.setAlignment(SWT.LEFT);
		column2.setText("Iteration");
		column2.setWidth(60);
		TreeColumn column3 = new TreeColumn(variableTree, SWT.RIGHT);
		column3.setAlignment(SWT.LEFT);
		column3.setText("Location");
		column3.setWidth(120);

		viewer.expandAll();
		contProv = new LocationTraceContentProvider();
		viewer.setLabelProvider(new LocationTraceLabelProvider());
		viewer.setContentProvider(contProv);

		// The List-Selections are published.
		// This is important for the Location-Stack
		getSite().setSelectionProvider(viewer);
		getViewSite().getPage().addSelectionListener(this);

		createActions();
		createToolbar();
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

	@Override
	public void selectionChanged(IWorkbenchPart part, ISelection selection) {
		if (selection instanceof ITreeSelection && part instanceof ResultList) {
			Object first = ((ITreeSelection) selection).getFirstElement();
			if (first instanceof IResult) {
				IEditorPart edPart = getSite().getPage().getActiveEditor();
				actualAllowedInput = edPart.getTitle();
				viewer.setInput(first);
				clearMarkedLocationsInEditor();
				markLocationsInEditor((IResult) first, edPart.getEditorInput(),
						edPart);
			} else {
				viewer.getTree().removeAll();
				clearMarkedLocationsInEditor();
			}
		} else if (selection instanceof ITreeSelection
				&& part instanceof LocationTrace) {
			Object first = ((ITreeSelection) selection).getFirstElement();
			if (first instanceof TraceNode) {
				TraceNode tn = (TraceNode) first;
				CACSLLocation loc = (CACSLLocation) tn.getLocation();
				IEditorPart editorPart = getSite().getPage().getActiveEditor();
				markLine(editorPart,
						getLineInformation(editorPart, loc.getStartLine()));
			}
		} else if (selection instanceof ITextSelection
				&& part instanceof EditorPart) {
			String text = ((EditorPart) part).getTitle();
			if (!text.equals(actualAllowedInput)) {
				viewer.getTree().removeAll();
				clearMarkedLocationsInEditor();
			}
		} else if (selection instanceof ITreeSelection
				&& part instanceof CommonNavigator) {
			CommonNavigator navi = (CommonNavigator) part;
			if (navi.isLinkingEnabled()) {
				if (((ITreeSelection) selection).getFirstElement() != null) {
					String text = ((ITreeSelection) selection)
							.getFirstElement().toString();
					if (!text.equals(actualAllowedInput)) {
						viewer.getTree().removeAll();
						clearMarkedLocationsInEditor();
					}
				} else {
					viewer.getTree().removeAll();
					clearMarkedLocationsInEditor();
				}
			}
		}
	}

	/**
	 * This method selects the given line, with the intern
	 * selectAndReveal-method.
	 * 
	 * @param editorPart
	 *            the active editor part
	 * @param lineNumber
	 *            the current line number
	 */
	private void markLine(IEditorPart editorPart, IRegion lineInfo) {
		if (!(editorPart instanceof ITextEditor)) {
			return;
		}
		ITextEditor editor = (ITextEditor) editorPart;
		if (lineInfo != null) {
			editor.selectAndReveal(lineInfo.getOffset(), lineInfo.getLength());
		}
	}

	/**
	 * For each Location in the given Failure-Path we create a LocationMarker.
	 * Each LocationMarker is reflected with an annotation, which has a certain
	 * style, so for example highlighting or boxes.
	 * 
	 * @param res
	 *            the given result
	 * @param input
	 *            the given editor input.
	 * @param editorPart
	 *            the active editor
	 */
	private void markLocationsInEditor(IResult res, IEditorInput input,
			IEditorPart editorPart) {
		if (res instanceof CounterExampleResult
				&& input instanceof IFileEditorInput) {
			for (ILocation loc : ((CounterExampleResult<?>) res).getFailurePath()) {
				if (loc instanceof CACSLLocation) {
					try {
						IRegion lineInfo = getLineInformation(editorPart,
								loc.getStartLine());
						IMarker marker = ((IFileEditorInput) input)
								.getFile()
								.createMarker(
										"de.uni_freiburg.informatik.ultimate.cdt.marker.locationmarker");
						marker.setAttribute(IMarker.LINE_NUMBER,
								loc.getStartLine());
						marker.setAttribute(IMarker.CHAR_START,
								lineInfo.getOffset());
						marker.setAttribute(IMarker.CHAR_END,
								lineInfo.getOffset() + lineInfo.getLength());
						displayedMarkerList.add(marker);
					} catch (CoreException e) {
						e.printStackTrace();
					}
				}
			}
		} else {
			clearMarkedLocationsInEditor();
		}
	}

	/**
	 * This method clears the displayed markers, this happens if the selection
	 * changes.
	 */
	private void clearMarkedLocationsInEditor() {
		for (IMarker marker : this.displayedMarkerList) {
			try {
				marker.delete();
			} catch (CoreException e) {
				e.printStackTrace();
			}
		}
	}

	/**
	 * This method returns us the line offset, which is used to display the
	 * highlighting right. Basically this is done with the editor input.
	 * 
	 * @param editorPart
	 *            the active editor
	 * @param lineNumber
	 *            the current line number
	 * @return line information containing the offset
	 */
	private IRegion getLineInformation(IEditorPart editorPart, int lineNumber) {
		if (!(editorPart instanceof ITextEditor) || lineNumber <= 0) {
			return null;
		}
		ITextEditor editor = (ITextEditor) editorPart;
		IDocument document = editor.getDocumentProvider().getDocument(
				editor.getEditorInput());
		if (document != null) {
			IRegion lineInfo = null;
			try {
				// line count internaly starts with 0, and not with 1 like in
				// GUI
				lineInfo = document.getLineInformation(lineNumber - 1);
			} catch (BadLocationException e) {
				// ignored because line number may not really exist in document,
				// we guess this...
			}
			return lineInfo;
		}
		return null;
	}

	/**
	 * This method creates the Actions for the Forward and Backward Button in
	 * the Toolbar Menu.
	 */
	private void createActions() {
		// Forward
		stepForward = new Action("Forward") {
			public void run() {
				moveSelection(false);
			}
		};
		stepForward.setImageDescriptor(getImageDescriptor("forward.PNG"));
		// Backward
		stepBackward = new Action("Backward") {
			public void run() {
				moveSelection(true);
			}
		};
		stepBackward.setImageDescriptor(getImageDescriptor("backward.PNG"));
	}

	/**
	 * This method moves the Selection, depending on the boolean flag back,
	 * forward or backward, both is possible. Basically this method is called by
	 * the Actions for our Toolbar-Buttons.
	 * 
	 * @param back
	 *            decides if we go back or for
	 */
	private void moveSelection(boolean back) {
		ITreeSelection selection = (ITreeSelection) viewer.getSelection();
		Object[] items = contProv.getElements(selection.getFirstElement());
		Object forward = null;
		Object backward = null;
		int position = -1;
		for (int i = 0; i < items.length; i++) {
			if (items[i].equals(selection.getFirstElement())) {
				position = i;
				break;
			}
		}
		// check if i + 1 is still in Range
		if (position + 1 < items.length) {
			forward = items[position + 1];
		}
		if (position - 1 >= 0) {
			backward = items[position - 1];
		}
		if (back) {
			if (backward != null) {
				viewer.setSelection(new StructuredSelection(backward), true);
			}
		} else {
			if (forward != null) {
				viewer.setSelection(new StructuredSelection(forward), true);
			}
		}

	}

	/**
	 * Create toolbar.
	 */
	private void createToolbar() {
		IToolBarManager mgr = getViewSite().getActionBars().getToolBarManager();
		mgr.add(stepBackward);
		mgr.add(stepForward);
	}

	/**
	 * Returns the image descriptor with the given relative path.
	 */
	private ImageDescriptor getImageDescriptor(String relativePath) {
		String iconPath = "icons/";
		Bundle bundle = Platform.getBundle(Activator.PLUGIN_ID);
		URL url = FileLocator.find(bundle, new Path(iconPath + relativePath),
				null);
		return ImageDescriptor.createFromURL(url);
	}

}
