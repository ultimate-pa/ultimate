package de.uni_freiburg.informatik.ultimate.gui;

import de.uni_freiburg.informatik.ultimate.gui.views.LoggingView;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;

public class UltimateDefaultPerspective implements IPerspectiveFactory {

	public static final String ID = "de.uni_freiburg.informatik.ultimate.gui.UltimateDefaultPerspective";
	public static final String FOLDER_RIGHT =ID + ".FolderRight";
	public static final String FOLDER_LEFT =ID + ".FolderLeft";
	public static final String FOLDER_BOTTOM =ID + ".FolderBottom";
	
	public void createInitialLayout(IPageLayout layout) {

		String editorAreaId = layout.getEditorArea();
		layout.setEditorAreaVisible(true);
		layout.setFixed( false );
        layout.createPlaceholderFolder( FOLDER_RIGHT, IPageLayout.RIGHT, 0.8f, editorAreaId );
        layout.createPlaceholderFolder( FOLDER_LEFT,IPageLayout.LEFT, 0.8f, editorAreaId );
        layout.createPlaceholderFolder( FOLDER_BOTTOM, IPageLayout.BOTTOM, 0.8f, editorAreaId );
        
		layout.addView(LoggingView.ID, IPageLayout.BOTTOM, 0.5f, FOLDER_BOTTOM);
	}
}
