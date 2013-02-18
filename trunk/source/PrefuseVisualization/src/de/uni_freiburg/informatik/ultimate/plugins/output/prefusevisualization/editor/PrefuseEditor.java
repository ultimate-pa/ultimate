package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.editor;

import java.awt.Frame;

import javax.swing.UIManager;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.export.DisplayExport;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.gui.PrefusePanel;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.gui.ResizeAction;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.selection.PrefuseSelectionProvider;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.awt.SWT_AWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;

import prefuse.Display;
import prefuse.util.ui.UILib;

/**
 * the editor part for prefuse
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate$
 * $LastChangedBy$
 * $LastChangedRevision$
 */
public class PrefuseEditor extends EditorPart {
	private Display m_Display = null;
	private String label = "p r e f u s e";

	public static final String ID = "de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.editor.PrefuseEditor";

	static {
		try {
			UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
		} catch (Exception e) {
			e.toString();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.EditorPart#doSave(org.eclipse.core.runtime.IProgressMonitor)
	 */
	public void doSave(IProgressMonitor monitor) {
		DisplayExport dEx = new DisplayExport(m_Display);
		dEx.save();

	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.EditorPart#doSaveAs()
	 */
	public void doSaveAs() {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.EditorPart#init(org.eclipse.ui.IEditorSite,
	 *      org.eclipse.ui.IEditorInput)
	 */
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		setSite(site);
		setInput(input);
		setPartName(((PrefuseEditorInput) input).getName());

		m_Display = ((PrefuseEditorInput) input).getDisplay();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.EditorPart#isDirty()
	 */
	public boolean isDirty() {
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.EditorPart#isSaveAsAllowed()
	 */
	public boolean isSaveAsAllowed() {
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	public void createPartControl(Composite parent) {

		org.eclipse.swt.widgets.Composite comp = new Composite(parent,
				SWT.EMBEDDED);
		Frame awt = SWT_AWT.new_Frame(comp);

		UILib.setPlatformLookAndFeel();

		ResizeAction rz = new ResizeAction(m_Display);
		awt.addComponentListener(rz);

		PrefusePanel prefusePanel = new PrefusePanel(m_Display, label);

		PrefuseSelectionProvider selectionprovider = new PrefuseSelectionProvider(
				getEditorInput());

		prefusePanel.addSelectionListener(selectionprovider);

		getSite().setSelectionProvider(selectionprovider);

		awt.add(prefusePanel);
	}

	/**
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	//@Override
	public void setFocus() {
	}
}