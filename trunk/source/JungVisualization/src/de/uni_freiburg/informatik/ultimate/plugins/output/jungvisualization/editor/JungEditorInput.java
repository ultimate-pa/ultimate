package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor;

import java.util.concurrent.atomic.AtomicInteger;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IPersistableElement;

import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions.MenuActions.Mode;
import edu.uci.ics.jung.visualization.VisualizationViewer;

/**
 * EditorInput for the {@link JungEditor}.
 * 
 * @see {@link IEditorInput}
 * @author lena
 * 
 */
public class JungEditorInput implements IEditorInput {

	private static AtomicInteger mNextFreeId = new AtomicInteger();
	private final String mName;
	private final VisualizationViewer<VisualizationNode, VisualizationEdge> mVisualizationViewer;
	private final String mId;
	private Mode mCurrentMode;

	/**
	 * @param name
	 *            The name of the EditorInput.
	 * @param visualizationViewer
	 */
	public JungEditorInput(String name, VisualizationViewer<VisualizationNode, VisualizationEdge> visualizationViewer) {
		assert name != null;
		mName = name;
		mVisualizationViewer = visualizationViewer;
		mId = String.valueOf(mNextFreeId.incrementAndGet());
		mCurrentMode = Mode.PICKING;
	}

	public VisualizationViewer<VisualizationNode, VisualizationEdge> getViewer() {
		return mVisualizationViewer;
	}
	
	public Mode getMode(){
		return mCurrentMode;
	}
	
	public void setMode(Mode mode){
		mCurrentMode = mode;
	}
	
	public String getId(){
		return mId;
	}

	@Override
	public boolean exists() {
		return false;
	}

	@Override
	public ImageDescriptor getImageDescriptor() {
		return null;
	}

	@Override
	public String getName() {
		return mName;
	}

	@Override
	public IPersistableElement getPersistable() {
		return null;
	}

	@Override
	public String getToolTipText() {
		return "";
	}

	@SuppressWarnings("rawtypes")
	@Override
	public Object getAdapter(Class adapter) {
		return null;
	}
	
	/**
	 * Hacky shit (based on Lenas code; didnt want to learn how to do that properly) 
	 */
	public void displayContextMenu(){
		
	}

}
