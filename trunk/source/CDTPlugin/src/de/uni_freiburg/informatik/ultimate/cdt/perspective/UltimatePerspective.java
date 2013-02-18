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
		String editorArea = layout.getEditorArea();

		// Place navigator and outline to left of
		// editor area.
		IFolderLayout left = layout.createFolder("left", IPageLayout.LEFT,
				(float) 0.2, editorArea);
		left.addView(IPageLayout.ID_PROJECT_EXPLORER);

		// Here we declare what we place right of the editor area
		// First we use right1 to place the ResultList
		IFolderLayout right1 = layout.createFolder("right1", IPageLayout.RIGHT,
				(float) 0.7, editorArea);
		right1.addView(ResultList.ID);
		// Then we define right2 to place the LocationTrace
		IFolderLayout right2 = layout.createFolder("right2",
				IPageLayout.BOTTOM, (float) 0.2, "right1");
		right2.addView(LocationTrace.ID);
		// Now we add the VariableAssignment View under the LocationTrace
		IFolderLayout right3 = layout.createFolder("right3",
				IPageLayout.BOTTOM, (float) 0.5, "right2");
		right3.addView(VariableAssignment.ID);

		// Here is what we place under the editor area
		IFolderLayout bottom = layout.createFolder("bottom",
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
