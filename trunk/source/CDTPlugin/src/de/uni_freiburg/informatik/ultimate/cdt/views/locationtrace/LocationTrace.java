/*
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CDTPlugin plug-in.
 * 
 * The ULTIMATE CDTPlugin plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CDTPlugin plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTPlugin plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTPlugin plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CDTPlugin plug-in grant you additional permission
 * to convey the resulting work.
 */
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.views.resultlist.ResultList;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

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
	public static final String ID = "de.uni_freiburg.informatik.ultimate.cdt.LocationTrace";

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
	private final List<IMarker> displayedMarkerList = new ArrayList<IMarker>();

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
	public void createPartControl(final Composite parent) {
		final Tree variableTree = new Tree(parent, SWT.BORDER | SWT.H_SCROLL
				| SWT.V_SCROLL | SWT.FULL_SELECTION);
		variableTree.setHeaderVisible(true);
		viewer = new TreeViewer(variableTree);

		final TreeColumn column1 = new TreeColumn(variableTree, SWT.LEFT);
		column1.setAlignment(SWT.LEFT);
		column1.setText("Nr.");
		column1.setWidth(60);
		final TreeColumn column2 = new TreeColumn(variableTree, SWT.RIGHT);
		column2.setAlignment(SWT.LEFT);
		column2.setText("Iteration");
		column2.setWidth(60);
		final TreeColumn column3 = new TreeColumn(variableTree, SWT.RIGHT);
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
	public void selectionChanged(final IWorkbenchPart part, final ISelection selection) {
		if (selection instanceof ITreeSelection && part instanceof ResultList) {
			final Object first = ((ITreeSelection) selection).getFirstElement();
			if (first instanceof IResult) {
				final IEditorPart edPart = getSite().getPage().getActiveEditor();
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
			final Object first = ((ITreeSelection) selection).getFirstElement();
			if (first instanceof TraceNode) {
				final TraceNode tn = (TraceNode) first;
				final ILocation loc = tn.getLocation();
				final IEditorPart editorPart = getSite().getPage().getActiveEditor();
				markLine(editorPart,
						getLineInformation(editorPart, loc.getStartLine()));
			}
		} else if (selection instanceof ITextSelection
				&& part instanceof EditorPart) {
			final String text = ((EditorPart) part).getTitle();
			if (!text.equals(actualAllowedInput)) {
				viewer.getTree().removeAll();
				clearMarkedLocationsInEditor();
			}
		} else if (selection instanceof ITreeSelection
				&& part instanceof CommonNavigator) {
			final CommonNavigator navi = (CommonNavigator) part;
			if (navi.isLinkingEnabled()) {
				if (((ITreeSelection) selection).getFirstElement() != null) {
					final String text = ((ITreeSelection) selection)
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
	private void markLine(final IEditorPart editorPart, final IRegion lineInfo) {
		if (!(editorPart instanceof ITextEditor)) {
			return;
		}
		final ITextEditor editor = (ITextEditor) editorPart;
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
	private void markLocationsInEditor(final IResult res, final IEditorInput input,
			final IEditorPart editorPart) {
		if (res instanceof CounterExampleResult
				&& input instanceof IFileEditorInput) {
			for (final ILocation loc : ((CounterExampleResult<?,?,?>) res).getFailurePath()) {
				if (loc instanceof LocationFactory) {
					try {
						final IRegion lineInfo = getLineInformation(editorPart,
								loc.getStartLine());
						final IMarker marker = ((IFileEditorInput) input)
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
					} catch (final CoreException e) {
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
		for (final IMarker marker : displayedMarkerList) {
			try {
				marker.delete();
			} catch (final CoreException e) {
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
	private IRegion getLineInformation(final IEditorPart editorPart, final int lineNumber) {
		if (!(editorPart instanceof ITextEditor) || lineNumber <= 0) {
			return null;
		}
		final ITextEditor editor = (ITextEditor) editorPart;
		final IDocument document = editor.getDocumentProvider().getDocument(
				editor.getEditorInput());
		if (document != null) {
			IRegion lineInfo = null;
			try {
				// line count internaly starts with 0, and not with 1 like in
				// GUI
				lineInfo = document.getLineInformation(lineNumber - 1);
			} catch (final BadLocationException e) {
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
			@Override
			public void run() {
				moveSelection(false);
			}
		};
		stepForward.setImageDescriptor(getImageDescriptor("forward.PNG"));
		// Backward
		stepBackward = new Action("Backward") {
			@Override
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
	private void moveSelection(final boolean back) {
		final ITreeSelection selection = (ITreeSelection) viewer.getSelection();
		final Object[] items = contProv.getElements(selection.getFirstElement());
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
		final IToolBarManager mgr = getViewSite().getActionBars().getToolBarManager();
		mgr.add(stepBackward);
		mgr.add(stepForward);
	}

	/**
	 * Returns the image descriptor with the given relative path.
	 */
	private ImageDescriptor getImageDescriptor(final String relativePath) {
		final String iconPath = "icons/";
		final Bundle bundle = Platform.getBundle(Activator.PLUGIN_ID);
		final URL url = FileLocator.find(bundle, new Path(iconPath + relativePath),
				null);
		return ImageDescriptor.createFromURL(url);
	}

}
