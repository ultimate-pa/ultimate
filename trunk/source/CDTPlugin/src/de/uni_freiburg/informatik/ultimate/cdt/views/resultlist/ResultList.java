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
package de.uni_freiburg.informatik.ultimate.cdt.views.resultlist;

import java.util.HashSet;

import org.eclipse.cdt.internal.core.model.TranslationUnit;
import org.eclipse.core.resources.IFile;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.navigator.CommonNavigator;
import org.eclipse.ui.part.EditorPart;
import org.eclipse.ui.part.ViewPart;

/**
 * This is one of the first Views for presenting CounterExamples to the user.
 * Here we list up all feasible CounterExamples for the current viewed File.
 * 
 * @author Stefan Wissert
 * 
 */
public class ResultList extends ViewPart implements ISelectionListener {

	public static final String ID = "de.uni_freiburg.informatik.ultimate.cdt.ResultList";

	/**
	 * The underlying JFace Component
	 */
	private TreeViewer viewer;

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
		column1.setText("Line Nr.");
		column1.setWidth(60);
		final TreeColumn column2 = new TreeColumn(variableTree, SWT.RIGHT);
		column2.setAlignment(SWT.LEFT);
		column2.setText("Description");
		column2.setWidth(120);
		final TreeColumn column3 = new TreeColumn(variableTree, SWT.RIGHT);
		column3.setAlignment(SWT.LEFT);
		column3.setText("Location");
		column3.setWidth(120);

		viewer.expandAll();
		viewer.setContentProvider(new ResultListContentProvider());
		// We set here a new LabelProvider to display the Results
		// in a human readable manner.
		viewer.setLabelProvider(new ResultListLabelProvider());
		// The List-Selections are published.
		// This is important for the Location-Stack
		getSite().setSelectionProvider(viewer);
		// we add this object as selection listener
		getViewSite().getPage().addSelectionListener(this);
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
		// First we check the Selection of the Editor
		// Second is the Selection of the ProjectExplorer
		if (selection instanceof ITextSelection && part instanceof EditorPart) {
			final EditorPart edPart = (EditorPart) part;
			IFile file = null;
			// Because we store the results per file, we need the correct
			// results
			// ---> so we need to get the original file from the system
			if (edPart.getEditorInput() instanceof IFileEditorInput) {
				final IFileEditorInput fei = (IFileEditorInput) edPart
						.getEditorInput();
				file = fei.getFile();
			}
			if (file != null && file.getFileExtension().equals("c")) {
				viewer.setInput(file.getLocation().toOSString());
			} else {
				viewer.setInput("");
			}
		} else if (selection instanceof ITreeSelection
				&& part instanceof CommonNavigator) {
			final CommonNavigator navi = (CommonNavigator) part;
			// we only delete our Selection if Linking with Navigator is enabled
			if (navi.isLinkingEnabled()) {
				if (((ITreeSelection) selection).getFirstElement() != null) {
					IFile file = null;
					final Object firstElement = ((ITreeSelection) selection)
							.getFirstElement();
					if (firstElement instanceof TranslationUnit) {
						file = ((TranslationUnit) firstElement).getFile();
					}
					// get all current opened files, we only show results for
					// them
					final HashSet<String> currentFilesOpened = new HashSet<String>();
					for (final IEditorReference ed : getSite().getPage()
							.getEditorReferences()) {
						try {
							if (ed.getEditorInput() instanceof IFileEditorInput) {
								final IFileEditorInput fei = (IFileEditorInput) ed
										.getEditorInput();
								currentFilesOpened.add(fei.getFile()
										.getLocation().toOSString());
							}
						} catch (final PartInitException e) {
							e.printStackTrace();
						}
					}
					if (file != null
							&& currentFilesOpened.contains(file.getLocation()
									.toOSString())
							&& file.getFileExtension().equals("c")) {
						viewer.setInput(file.getLocation().toOSString());
					} else {
						viewer.setInput("");
					}
				}
			}
		}
	}

	/**
	 * @param filename
	 */
	public void setViewerInput(final String filename) {
		viewer.setInput(filename);
	}
}
