package local.stalin.plugins.output.jungvisualization.selection;

import java.util.ArrayList;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;

/**
 * Local ISelectionProvider, provides access to the actual JungSelection for the workbench.
 * @see {@link ISelectionProvider}
 * @author lena
 *
 */
public class JungSelectionProvider implements ISelectionProvider {

	private ArrayList<ISelectionChangedListener> listeners = new ArrayList<ISelectionChangedListener>();;
	private JungSelection jungSelection;
	
	@Override
	public void addSelectionChangedListener(ISelectionChangedListener listener) {
		listeners.add(listener);
	}

	@Override
	public ISelection getSelection() {
		return (ISelection) this.jungSelection;
	}

	@Override
	public void removeSelectionChangedListener(ISelectionChangedListener listener) {
			listeners.remove(listener);
	}

	@Override
	public void setSelection(ISelection selection) {
		if (selection instanceof JungSelection) {
			this.jungSelection = (JungSelection) selection;
		}
		
	}
	
	/**
	 * fires an Selection Event
	 */
	public void fireSelectionEvent() {
		if (this.jungSelection != null) {

			for (ISelectionChangedListener listener : listeners) {

				listener.selectionChanged(new SelectionChangedEvent(this,(ISelection) this.jungSelection));
			}
		}
	}

}
