package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.selection;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.editor.PrefuseEditorInput;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.ui.IEditorInput;

/**
 * manage the selection events
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate$
 * $LastChangedBy$
 * $LastChangedRevision$
 */
public class PrefuseSelectionProvider implements ISelectionProvider {

	private final PrefuseEditorInput m_Input;
	private ArrayList<ISelectionChangedListener> listeners;
	private PrefuseSelection prefuseSelection;

	/**
	 * create and register n new provider
	 * 
	 * @param input the prefuseEditor input
	 * @throws IllegalArgumentException
	 */
	public PrefuseSelectionProvider(IEditorInput input)
			throws IllegalArgumentException {
		if (!(input instanceof PrefuseEditorInput)) {
			throw new IllegalArgumentException(
					"IEditorInput is not an instance of PrefuseEditorInput");
		} else {
			m_Input = (PrefuseEditorInput) input;
		}
		this.prefuseSelection = new PrefuseSelection();
		listeners = new ArrayList<ISelectionChangedListener>();
	}

	/**
	 * fire click event
	 * 
	 * @param uid
	 *            the UID of the Note creating the event
	 */
	public void itemClicked(String uid) {
		this.prefuseSelection.setPayload(UltimateServices.getInstance().search(this.m_Input.getGraphType(),
				uid));
		this.fireSelectionEvent();
	}

	/**
	 * fire click event
	 */
	public void itemClicked() {
		this.prefuseSelection.setPayload(null);
		this.fireSelectionEvent();
	}

	/**
	 * @see org.eclipse.jface.viewers.ISelectionProvider#addSelectionChangedListener(org.eclipse.jface.viewers.ISelectionChangedListener)
	 */
	public void addSelectionChangedListener(ISelectionChangedListener listener) {
		listeners.add(listener);
	}

	/**
	 * @see org.eclipse.jface.viewers.ISelectionProvider#getSelection()
	 */
	public ISelection getSelection() {
		return (ISelection) this.prefuseSelection;
	}

	/**
	 * @see org.eclipse.jface.viewers.ISelectionProvider#removeSelectionChangedListener(org.eclipse.jface.viewers.ISelectionChangedListener)
	 */
	public void removeSelectionChangedListener(
			ISelectionChangedListener listener) {
		listeners.remove(listener);
	}

	/**
	 * @see org.eclipse.jface.viewers.ISelectionProvider#setSelection(org.eclipse.jface.viewers.ISelection)
	 */
	public void setSelection(ISelection selection) {
		if (selection instanceof PrefuseSelection) {
			this.prefuseSelection = (PrefuseSelection) selection;
		}
	}

	/**
	 * fires an Selection Event
	 */
	public void fireSelectionEvent() {
		if (this.prefuseSelection != null) {

			for (ISelectionChangedListener listener : listeners) {

				listener.selectionChanged(new SelectionChangedEvent(this,
						(ISelection) this.prefuseSelection));
			}
		}
	}
}