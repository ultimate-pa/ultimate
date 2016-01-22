/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.result.model.IResult;
import de.uni_freiburg.informatik.ultimate.result.model.IResultWithLocation;

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
		viewer = new TextViewer(parent, SWT.BORDER | SWT.H_SCROLL | SWT.V_SCROLL | SWT.FULL_SELECTION);
		viewer.setEditable(false);
		ISelectionService ser = (ISelectionService) getSite().getService(ISelectionService.class);
		ser.addSelectionListener(new ISelectionListener() {
			public void selectionChanged(IWorkbenchPart part, ISelection selection) {
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
			Object firstElement = ((IStructuredSelection) selection).getFirstElement();
			IMarker marker = null;
			if (firstElement instanceof IAdaptable) {
				marker = (IMarker) ((IAdaptable) firstElement).getAdapter(IMarker.class);
			} else if (firstElement instanceof IMarker) {
				marker = (IMarker) firstElement;
			}
			if (marker != null) {
				queryProviders(marker);
			}
		}
	}

	private StringBuilder makeResultViewString(IResult result, int maxLength) {
		StringBuilder sb = new StringBuilder();
		String lineSeparator = System.getProperty("line.separator");
		sb.append("Short Description:");
		sb.append(lineSeparator);
		sb.append(breakLines(result.getShortDescription(), lineSeparator, maxLength));
		sb.append(lineSeparator);
		sb.append(lineSeparator);
		sb.append("Long Description:");
		sb.append(breakLines(result.getLongDescription(), lineSeparator, maxLength));
		sb.append(lineSeparator);
		return sb;
	}

	private String breakLines(String s, String breaker, int maxLength) {
//		String[] parts = s.split(" ");
//		StringBuilder sb = new StringBuilder();
//
//		int actualLength = 0;
//		for (String part : parts) {
//			actualLength = actualLength + part.length();
//			if (actualLength > maxLength) {
//				sb.append(breaker);
//				actualLength = part.length();
//			}
//			sb.append(part);
//			sb.append(" ");
//		}
//
//		return sb.toString();
		return s;
	}

	private void queryProviders(IMarker marker) {
		IResult result = extractResultFromMarker(marker);
		if (result != null) {
			int length = viewer.getControl().getBounds().width;
			
			StringBuilder sb = makeResultViewString(result, length);
			Document doc = new Document(sb.toString());
			viewer.setDocument(doc);
			return;
		}
		// FIXME: This is the old approach...
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
			sb.append("Result found in " + foundRes.getLocation().getFileName() + " in Line: "
					+ foundRes.getLocation().getStartLine());
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

	private IResult extractResultFromMarker(IMarker marker) {

		// The args attribute has the following form:
		//
		// #Tue Apr 08 21:42:00 CEST 2014
		// len=2
		// a1=de.uni_freiburg.informatik.ultimate.result.BenchmarkResult@62303b81
		// a0=Ultimate Automizer benchmark data

		String args = marker.getAttribute("args", null);
		if (args == null) {
			return null;
		}

		String[] components = args.split("\n");
		if (components.length <= 2) {
			return null;
		}
		// this can be used to find the maximal length of this strange construct
		// int length = Integer.parseInt(components[1].split("=")[1]);

		int uid = Integer.parseInt(components[2].split("=")[1].trim());
		return CDTResultStore.getHackyResult(uid);
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
