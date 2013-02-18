package local.stalin.gui.logging;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IPersistableElement;

/**
 * basic Editor input .. no functionality..
 * equals distinquishes between GuiLoggingWindows objects 
 * for keeping this unique
 * 
 * @author Christian Ortolf
 *
 */
public class LoggingEditorInput implements IEditorInput {

private final GuiLoggingWindow logw;

	public LoggingEditorInput(GuiLoggingWindow logw){
		this.logw=logw;
	}
	
	public boolean exists() {
		return false;
	}

	public ImageDescriptor getImageDescriptor() {
		return null;
	}

	public String getName() {
		return "Gui Logging Window";
	}

	public IPersistableElement getPersistable() {
		return null;
	}

	public String getToolTipText() {
		return getName();
	}

	@SuppressWarnings("unchecked")
	public Object getAdapter(Class adapter) {
		return null;
	}

	
	//@Override
	public int hashCode() {
		final int PRIME = 31;
		int result = 1;
		result = PRIME * result + ((logw == null) ? 0 : logw.hashCode());
		return result;
	}

	//@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final LoggingEditorInput other = (LoggingEditorInput) obj;
		if (logw == null) {
			if (other.logw != null)
				return false;
		} else if (!logw.equals(other.logw))
			return false;
		return true;
	}
	
	

}
