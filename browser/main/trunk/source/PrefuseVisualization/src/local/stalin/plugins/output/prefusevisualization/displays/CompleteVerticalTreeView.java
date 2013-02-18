package local.stalin.plugins.output.prefusevisualization.displays;

import java.awt.geom.Point2D;

import local.stalin.plugins.output.prefusevisualization.actions.AutoPanAction;
import local.stalin.plugins.output.prefusevisualization.actions.EdgeLabel;
import local.stalin.plugins.output.prefusevisualization.actions.TextMarkAction;
import local.stalin.plugins.output.prefusevisualization.actions.NodeMarkAction;
import local.stalin.plugins.output.prefusevisualization.gui.PrefuseColorSelection;
import local.stalin.plugins.output.prefusevisualization.gui.PrefuseFontSelection;

import prefuse.Constants;
import prefuse.Display;
import prefuse.Visualization;
import prefuse.action.ActionList;
import prefuse.action.ItemAction;
import prefuse.action.RepaintAction;
import prefuse.action.animate.ColorAnimator;
import prefuse.action.animate.LocationAnimator;
import prefuse.action.animate.QualityControlAnimator;
import prefuse.action.animate.VisibilityAnimator;
import prefuse.action.assignment.ColorAction;
import prefuse.action.assignment.FontAction;
import prefuse.action.layout.CollapsedSubtreeLayout;
import prefuse.action.layout.graph.NodeLinkTreeLayout;
import prefuse.activity.Activity;
import prefuse.activity.SlowInSlowOutPacer;
import prefuse.controls.FocusControl;
import prefuse.controls.PanControl;
import prefuse.controls.WheelZoomControl;
import prefuse.controls.ZoomControl;
import prefuse.controls.ZoomToFitControl;
import prefuse.data.Graph;
import prefuse.render.DefaultRendererFactory;
import prefuse.render.EdgeRenderer;
import prefuse.render.AbstractShapeRenderer;
import prefuse.render.LabelRenderer;
import prefuse.visual.VisualItem;
import prefuse.visual.sort.TreeDepthItemSorter;

/**
 * create an complete TreeView
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate: 2008-03-07 13:50:06 +0100 (Fr, 07 Mrz 2008) $
 * $LastChangedBy: keilr $
 * $LastChangedRevision: 495 $
 */
public class CompleteVerticalTreeView extends Display {

	private static final long serialVersionUID = 1L;
	private static final String tree = "tree";
	private static final String treeNodes = "tree.nodes";
	private static final String treeEdges = "tree.edges";

	private LabelRenderer m_nodeRenderer;
	private EdgeRenderer m_edgeRenderer;

	private int m_orientation = Constants.ORIENT_TOP_BOTTOM;

	private PrefuseFontSelection prefuseFontSelection = new PrefuseFontSelection();
	private PrefuseColorSelection prefuseColorSelection = new PrefuseColorSelection();

	/**
	 * @param graph
	 *            graph object to display
	 * @param label
	 *            label
	 */
	public CompleteVerticalTreeView(Graph graph, String label) {
		super(new Visualization());
		m_vis.add(tree, graph);

		m_nodeRenderer = new LabelRenderer("name");
		m_nodeRenderer.setRenderType(AbstractShapeRenderer.RENDER_TYPE_FILL);
		m_nodeRenderer.setRoundedCorner(8, 8);
		m_edgeRenderer = new EdgeRenderer(Constants.EDGE_TYPE_LINE,Constants.EDGE_ARROW_FORWARD);

		DefaultRendererFactory rf = new DefaultRendererFactory(m_nodeRenderer,m_edgeRenderer);
		//rf.add(new InGroupPredicate(treeEdges), m_edgeRenderer);
		m_vis.setRendererFactory(rf);

		m_vis.addDecorators("name", treeEdges, EdgeLabel.getDecorator());

		// colors
		ItemAction nodeColor = new NodeMarkAction(treeNodes);
		ItemAction textColor = new TextMarkAction(treeNodes);
		m_vis.putAction("textColor", textColor);

		ItemAction edgeColor = new ColorAction(treeEdges,
				VisualItem.STROKECOLOR, prefuseColorSelection
						.getEdgeStyleColor());

		// quick repaint
		ActionList repaint = new ActionList();
		repaint.add(nodeColor);
		repaint.add(new RepaintAction());
		m_vis.putAction("repaint", repaint);

		// full paint
		ActionList fullPaint = new ActionList();
		fullPaint.add(nodeColor);
		m_vis.putAction("fullPaint", fullPaint);

		// animate paint change
		ActionList animatePaint = new ActionList(400);
		animatePaint.add(new ColorAnimator(treeNodes));
		animatePaint.add(new RepaintAction());
		m_vis.putAction("animatePaint", animatePaint);

		// create the tree layout action
		NodeLinkTreeLayout treeLayout = new NodeLinkTreeLayout(tree,
				m_orientation, 5 * prefuseFontSelection.getDistanceFaktor(),
				0.5 * prefuseFontSelection.getDistanceFaktor(),
				1 * prefuseFontSelection.getDistanceFaktor());

		treeLayout.setLayoutAnchor(new Point2D.Double(300, 100)); // default
																	// point
		m_vis.putAction("treeLayout", treeLayout);

		CollapsedSubtreeLayout subLayout = new CollapsedSubtreeLayout(tree,
				m_orientation);
		m_vis.putAction("subLayout", subLayout);

		AutoPanAction autoPan = new AutoPanAction(this, m_orientation);

		// render edge labels
		ActionList layout = new ActionList(Activity.INFINITY);
		layout.add(new EdgeLabel("name"));
		layout.add(autoPan);
		m_vis.putAction("layout", layout);
		m_vis.run("layout");

		// create the filtering and layout
		ActionList filter = new ActionList();
		filter.add(new FontAction(treeNodes, prefuseFontSelection
						.getNodeFont()));
		filter.add(treeLayout);
		filter.add(subLayout);
		filter.add(textColor);
		filter.add(nodeColor);
		filter.add(edgeColor);
		m_vis.putAction("filter", filter);

		// animated transition
		ActionList animate = new ActionList(1000);
		animate.setPacingFunction(new SlowInSlowOutPacer());
		animate.add(autoPan);
		animate.add(new QualityControlAnimator());
		animate.add(new VisibilityAnimator(tree));
		animate.add(new LocationAnimator(treeNodes));
		animate.add(new ColorAnimator(treeNodes));
		animate.add(new RepaintAction());
		//m_vis.putAction("animate", animate);
		//m_vis.alwaysRunAfter("filter", "animate");

		// create animator for orientation changes
		ActionList orient = new ActionList(2000);
		orient.setPacingFunction(new SlowInSlowOutPacer());
		orient.add(autoPan);
		orient.add(new QualityControlAnimator());
		orient.add(new LocationAnimator(treeNodes));
		orient.add(new RepaintAction());
		//m_vis.putAction("orient", orient);

		// add action listener
		setItemSorter(new TreeDepthItemSorter());
		addControlListener(new ZoomToFitControl());
		addControlListener(new ZoomControl());
		addControlListener(new WheelZoomControl());
		addControlListener(new PanControl());
		addControlListener(new FocusControl(1, "filter"));

		m_vis.run("filter");
	}
}