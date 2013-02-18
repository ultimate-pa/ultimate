package local.stalin.SMTInterface.viewer;

import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.Writer;

import local.stalin.nativez3.Z3ProofRule;

import org.apache.batik.dom.GenericDOMImplementation;
import org.apache.batik.svggen.SVGGraphics2D;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.w3c.dom.DOMImplementation;
import org.w3c.dom.Document;

import edu.uci.ics.jung.visualization.VisualizationViewer;

public class SaveDisplayAction extends Action implements IWorkbenchWindowActionDelegate {

	public static final String ID = "local.stalin.SMTInterface.export.SaveDisplayAction";
	
	private IWorkbenchWindow mwindow;
	
	@Override
	public void dispose() {}

	@Override
	public void init(IWorkbenchWindow window) {
		mwindow = window;
	}

	@Override
	public void run(IAction action) {
		if (mwindow.getActivePage().getActiveEditor() == null)
			return;
		if (mwindow.getActivePage().getActiveEditor() instanceof ProofTreeEditor) {
			try {
				VisualizationViewer<Z3ProofRule,ProofTreeEditor.RuleNameHolder> vis = ((ProofTreeEditor)mwindow.getActivePage().getActiveEditor()).getViewer();
				FileDialog fd = new FileDialog(mwindow.getShell(), SWT.SAVE);
				String fp = fd.open();
				if( fp == null )
					return;
				vis.setDoubleBuffered(false);
				try {
					DOMImplementation domimpl = GenericDOMImplementation.getDOMImplementation();
					String svgNS = "http://www.w3.org/2000/svg";
					Document doc = domimpl.createDocument(svgNS,"svg",null);
					SVGGraphics2D svg = new SVGGraphics2D(doc);
					vis.paint(svg);
					FileOutputStream fis = new FileOutputStream(fp);
					Writer out = new OutputStreamWriter(fis,"UTF-8");
					svg.stream(out,true);
					fis.flush();
					fis.close();
				} finally {
					vis.setDoubleBuffered(true);
				}
			} catch (Throwable ex) {
				ex.printStackTrace(System.err);
			}
		}
	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {}

}
