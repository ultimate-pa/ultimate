package local.stalin.SMTInterface.viewer;

import java.awt.Dimension;
import java.awt.Frame;
import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.event.MouseEvent;

import javax.swing.JPanel;
import javax.swing.UIManager;

import local.stalin.nativez3.Z3ProofRule;

import org.apache.commons.collections15.Transformer;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.awt.SWT_AWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;

import edu.uci.ics.jung.algorithms.layout.BalloonLayout;
import edu.uci.ics.jung.algorithms.layout.CircleLayout;
import edu.uci.ics.jung.algorithms.layout.DAGLayout;
import edu.uci.ics.jung.algorithms.layout.FRLayout;
import edu.uci.ics.jung.algorithms.layout.FRLayout2;
import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.algorithms.layout.TreeLayout;
import edu.uci.ics.jung.graph.DelegateTree;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.uci.ics.jung.graph.Forest;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.Tree;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.control.CrossoverScalingControl;
import edu.uci.ics.jung.visualization.control.DefaultModalGraphMouse;
import edu.uci.ics.jung.visualization.control.ModalGraphMouse;
import edu.uci.ics.jung.visualization.control.PickingGraphMousePlugin;
import edu.uci.ics.jung.visualization.control.PluggableGraphMouse;
import edu.uci.ics.jung.visualization.control.ScalingGraphMousePlugin;
import edu.uci.ics.jung.visualization.control.TranslatingGraphMousePlugin;
import edu.uci.ics.jung.visualization.decorators.ToStringLabeller;

public class ProofTreeEditor extends EditorPart implements ComponentListener {
	
	final static class RuleNameHolder {
		String mrulename;
		public RuleNameHolder(Z3ProofRule pr) {
			mrulename = pr.getRuleName();
		}
		public String toString() {
			return mrulename;
		}
	}

	public static final String ID = "local.stalin.SMTInterface.viewer.ProofTreeEditor";
	
	static {
		try {
			UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
		} catch (Exception e) {
			e.toString();
		}
	}
	
	private VisualizationViewer<Z3ProofRule,RuleNameHolder> mvis; 
	
	@Override
	public void doSave(IProgressMonitor monitor) {}

	@Override
	public void doSaveAs() {
		
	}

	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		setSite(site);
		setInput(input);
		setPartName(((ProofTreeInput)input).getName());
	}

	@Override
	public boolean isDirty() {
		return false;
	}

	@Override
	public boolean isSaveAsAllowed() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void createPartControl(Composite parent) {
		Composite comp = new Composite(parent,SWT.EMBEDDED | SWT.H_SCROLL | SWT.V_SCROLL | SWT.RESIZE);
		comp.setSize(5000,2000);
		Frame frame = SWT_AWT.new_Frame(comp);
		Layout<Z3ProofRule,RuleNameHolder> layout = new FRLayout2<Z3ProofRule,RuleNameHolder>(createTree());
//		layout.setSize(new Dimension(1000,1000)); // sets the initial size of the space
		mvis = new VisualizationViewer<Z3ProofRule,RuleNameHolder>(layout);
		PluggableGraphMouse gm = new PluggableGraphMouse();
		gm.add(new TranslatingGraphMousePlugin(MouseEvent.BUTTON1_MASK));
		gm.add(new ScalingGraphMousePlugin(new CrossoverScalingControl(),0,1.1f,0.9f));
		gm.add(new PickingGraphMousePlugin<Z3ProofRule, RuleNameHolder>(MouseEvent.BUTTON2_MASK,MouseEvent.BUTTON2_MASK));
		mvis.setGraphMouse(gm);
//		mvis.setPreferredSize(new Dimension(2000,1000));
		mvis.setPreferredSize(new Dimension(parent.getShell().getSize().x,parent.getShell().getSize().y));
//		System.err.println("preferred size = " + mvis.getPreferredSize());
//		mvis.setPreferredSize(layout.getSize());
//		System.err.println("layout size is " + layout.getSize());
		mvis.getRenderContext().setVertexLabelTransformer(new Transformer<Z3ProofRule,String>() {

			@Override
			public String transform(Z3ProofRule arg0) {
				return arg0.getResult().toString();
			}
			
		});
		mvis.getRenderContext().setEdgeLabelTransformer(new ToStringLabeller<RuleNameHolder>());
//		System.err.println("mvis.getsize == " + mvis.getSize());
		JPanel p = new JPanel();
		p.add(mvis);
		//JScrollPane p = new JScrollPane(mvis);
//		p.setViewportView(mvis);
//		p.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_ALWAYS);
//		p.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS);
		p.setVisible(true);
		frame.add(p);
	}

	private final Graph<Z3ProofRule,RuleNameHolder> createTree() {
		DirectedSparseGraph<Z3ProofRule,RuleNameHolder> res = new DirectedSparseGraph<Z3ProofRule,RuleNameHolder>();
		Z3ProofRule root = ((ProofTreeInput)getEditorInput()).getRoot();
		res.addVertex(root);
		recursiveCreateTree(res,root);
		return res;
	}

	private final void recursiveCreateTree(
		DirectedSparseGraph<Z3ProofRule,RuleNameHolder> res, Z3ProofRule root) {
		for( Z3ProofRule child : root.getAntecedents() ) {
//			System.err.println("Adding edge " + root);
			res.addEdge(new RuleNameHolder(root),root,child);
			recursiveCreateTree(res,child);
		}
	}

	@Override
	public void setFocus() {}
	
	VisualizationViewer<Z3ProofRule,RuleNameHolder> getViewer() {
		return mvis;
	}

	@Override
	public void componentHidden(ComponentEvent e) {}

	@Override
	public void componentMoved(ComponentEvent e) {}

	@Override
	public void componentResized(ComponentEvent e) {
		mvis.setSize(e.getComponent().getWidth(),e.getComponent().getHeight());
		mvis.validate();
	}

	@Override
	public void componentShown(ComponentEvent e) {}

}
