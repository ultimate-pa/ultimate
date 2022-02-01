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
package de.uni_freiburg.informatik.ultimate.cdt.perspective;

import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.eclipse.ui.console.IConsoleConstants;

import de.uni_freiburg.informatik.ultimate.cdt.views.locationtrace.LocationTrace;
import de.uni_freiburg.informatik.ultimate.cdt.views.resultdetails.ResultDetails;
import de.uni_freiburg.informatik.ultimate.cdt.views.resultlist.ResultList;
import de.uni_freiburg.informatik.ultimate.cdt.views.variableassignment.VariableAssignment;

/**
 * In this class the default layout of the the UltimatePerspective is defined!
 * 
 * @author Stefan Wissert
 * 
 */
public class UltimatePerspective implements IPerspectiveFactory {

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.ui.IPerspectiveFactory#createInitialLayout(org.eclipse.ui
	 * .IPageLayout)
	 */
	@Override
	public void createInitialLayout(IPageLayout layout) {
		// Editors are placed for free.
		final String editorArea = layout.getEditorArea();

		// Place navigator and outline to left of
		// editor area.
		final IFolderLayout left = layout.createFolder("left", IPageLayout.LEFT,
				(float) 0.2, editorArea);
		left.addView(IPageLayout.ID_PROJECT_EXPLORER);

		// Here we declare what we place right of the editor area
		// First we use right1 to place the ResultList
		final IFolderLayout right1 = layout.createFolder("right1", IPageLayout.RIGHT,
				(float) 0.7, editorArea);
		right1.addView(ResultList.ID);
		// Then we define right2 to place the LocationTrace
		final IFolderLayout right2 = layout.createFolder("right2",
				IPageLayout.BOTTOM, (float) 0.2, "right1");
		right2.addView(LocationTrace.ID);
		// Now we add the VariableAssignment View under the LocationTrace
		final IFolderLayout right3 = layout.createFolder("right3",
				IPageLayout.BOTTOM, (float) 0.5, "right2");
		right3.addView(VariableAssignment.ID);

		// Here is what we place under the editor area
		final IFolderLayout bottom = layout.createFolder("bottom",
				IPageLayout.BOTTOM, (float) 0.7, editorArea);
		bottom.addView(IPageLayout.ID_PROBLEM_VIEW);
		bottom.addView(IPageLayout.ID_TASK_LIST);
		bottom.addView(IConsoleConstants.ID_CONSOLE_VIEW);
		bottom.addView(IPageLayout.ID_PROP_SHEET);
		// Discouraged access therefore we use the string here!
		// bottom.addView(ProblemDetails.ID);
		bottom.addView("org.eclipse.cdt.codan.internal.ui.views.ProblemDetails");
		bottom.addView(ResultDetails.ID);

	}
}
